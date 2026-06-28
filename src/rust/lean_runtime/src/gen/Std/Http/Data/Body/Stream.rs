// Lean compiler output
// Module: Std.Http.Data.Body.Stream
// Imports: Std.Sync Std.Async Std.Http.Data.Request Std.Http.Data.Response Std.Http.Data.Chunk Std.Http.Data.Body.Basic Std.Http.Data.Body.Any Init.Data.ByteArray
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_get___boxed, l_StateRefT_x27_instMonad___aux__13___boxed,
};
use crate::r#gen::Init::Data::ByteArray::Basic::l_ByteArray_isEmpty;
use crate::r#gen::Init::Data::ByteArray::{
    initialize_Init_Data_ByteArray, runtime_initialize_Init_Data_ByteArray,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_Name_mkStr4, l_instMonadLiftT___lam__0___boxed,
    l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::IO::l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed;
use crate::r#gen::Init::System::Promise::l_IO_Promise_resolve___boxed;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_set___boxed};
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_BaseAsync_lift___boxed, l_Std_Async_EAsync_instMonad,
    l_Std_Async_EAsync_instMonadFinally___lam__0___boxed,
    l_Std_Async_EAsync_instMonadLiftBaseAsync, l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Async::Select::l_Std_Async_Selectable_one___redArg;
use crate::r#gen::Std::Async::{initialize_Std_Async, runtime_initialize_Std_Async};
use crate::r#gen::Std::Http::Data::Body::Any::{
    initialize_Std_Http_Data_Body_Any, l_Std_Http_Body_Any_ofBody,
    l_Std_Http_Body_Any_ofBody___redArg, runtime_initialize_Std_Http_Data_Body_Any,
};
use crate::r#gen::Std::Http::Data::Body::Basic::{
    initialize_Std_Http_Data_Body_Basic, runtime_initialize_Std_Http_Data_Body_Basic,
};
use crate::r#gen::Std::Http::Data::Chunk::{
    initialize_Std_Http_Data_Chunk, l_Std_Http_Chunk_ofByteArray,
    runtime_initialize_Std_Http_Data_Chunk,
};
use crate::r#gen::Std::Http::Data::Request::{
    initialize_Std_Http_Data_Request, l_Std_Http_Request_Builder_body___redArg,
    runtime_initialize_Std_Http_Data_Request,
};
use crate::r#gen::Std::Http::Data::Response::{
    initialize_Std_Http_Data_Response, l_Std_Http_Response_Builder_body___redArg,
    runtime_initialize_Std_Http_Data_Response,
};
use crate::r#gen::Std::Sync::CancellationToken::l_Std_CancellationToken_selector;
use crate::r#gen::Std::Sync::Mutex::{l_Std_Mutex_atomically___redArg, l_Std_Mutex_new___redArg};
use crate::r#gen::Std::Sync::{initialize_Std_Sync, runtime_initialize_Std_Sync};
use crate::lean_imports_rs::Init::Core::{lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_copy_slice;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::lean_uint64_dec_lt;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_uint64_of_nat, lean_uint64_to_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_byte_array_size, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_as_task;
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
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
pub static l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 116, 116, 112, 0]};
static mut l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
pub static l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 100, 121, 0]};
static mut l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
pub static l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 101, 97, 109, 0]};
static mut l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
static l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__0_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__1_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject,12505880184336239166 as *mut LeanObject] };
static l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__2_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject,13864060453883145552 as *mut LeanObject] };
pub static l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__3_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject,10487113639549846819 as *mut LeanObject] };
static mut l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instImpl_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18_: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instTypeNameStream: *mut LeanObject = core::ptr::addr_of!(l_Std_Http_Body_instImpl___closed__4_00___x40_Std_Http_Data_Body_Stream_2871211244____hygCtx___hyg_18__value) as *mut LeanObject;
pub static l_Std_Http_Body_mkStream___closed__0_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 8) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Std_Http_Body_mkStream___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_mkStream___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_mkStream___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_mkStream___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_mkStream___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_mkStream___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1_value) as *mut LeanObject;
pub static l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_tryRecv___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_tryRecv___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_tryRecv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecv___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_tryRecvBody___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_tryRecvBody___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecvBody___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_tryRecvBody___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecvBody___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_tryRecvBody___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_tryRecvBody___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 99, 111, 110, 115, 117, 109, 101, 114, 32, 119, 97, 115, 32, 100, 114, 111, 112, 112, 101, 100, 0]};
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 18 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [111, 110, 108, 121, 32, 111, 110, 101, 32, 98, 108, 111, 99, 107, 101, 100, 32, 99, 111, 110, 115, 117, 109, 101, 114, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 0]};
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 18 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2_value) as *mut LeanObject;
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1_value
) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_recv___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_recv___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_recv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_recv___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_close___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Body_Stream_close___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_close___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_isClosed___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_isClosed___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_isClosed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__0_value) as *mut LeanObject;
static mut l_Std_Http_Body_Stream_isClosed___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_isClosed___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Body_Stream_isClosed___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_isClosed___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Stream_isClosed___closed__3_value: LeanClosureObject<0> =
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
static mut l_Std_Http_Body_Stream_isClosed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_isClosed___closed__4_value: LeanClosureObject<0> =
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
static mut l_Std_Http_Body_Stream_isClosed___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_isClosed___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_isClosed___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__5_value) as *mut LeanObject;
static mut l_Std_Http_Body_Stream_isClosed___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_isClosed___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Stream_isClosed___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadFinally___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_isClosed___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__7_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_isClosed___closed__8_value: LeanClosureObject<0> =
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
static mut l_Std_Http_Body_Stream_isClosed___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__8_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_isClosed___closed__9_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_isClosed___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__9_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_isClosed___closed__10_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_isClosed___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_isClosed___closed__10_value) as *mut LeanObject;
static mut l_Std_Http_Body_Stream_isClosed___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_isClosed___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Body_Stream_isClosed___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_isClosed___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Body_Stream_isClosed___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_isClosed___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Stream_getKnownSize___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_getKnownSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_getKnownSize___closed__0_value) as *mut LeanObject;
static mut l_Std_Http_Body_Stream_getKnownSize___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Stream_getKnownSize___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__1_value) as *mut LeanObject] };
static mut l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Stream_recvSelector___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_recvSelector___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Http_Body_Stream_recvSelector___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_recvSelector___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_recv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_instNextChunkAsync___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_Stream_instNextChunkAsync: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value: LeanClosureObject<
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
    m_fun: l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value: LeanClosureObject<
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
    m_fun: l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2_value: LeanClosureObject<
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
    m_fun: l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3_value: LeanClosureObject<
    3,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_Stream_instNextChunkContextAsync: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkContextAsync___closed__3_value)
        as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [98, 111, 100, 121, 32, 101, 120, 99, 101, 101, 100, 101, 100, 32, 109, 97, 120, 105, 109, 117, 109, 32, 115, 105, 122, 101, 32, 111, 102, 32, 0]};
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 98, 121, 116, 101, 115, 0]};
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [99, 104, 97, 110, 110, 101, 108, 32, 99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 18 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [111, 110, 108, 121, 32, 111, 110, 101, 32, 98, 108, 111, 99, 107, 101, 100, 32, 112, 114, 111, 100, 117, 99, 101, 114, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 0]};
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 18 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__2_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__3_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__4_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__6_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__7_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8_value) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value
) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3_value
) as *mut LeanObject;
pub static l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_hasInterest___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_hasInterest___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_hasInterest___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_hasInterest___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__0_value) as *mut LeanObject] };
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1_value: LeanCtorObject<1> =
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
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__0___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__0___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4_value: LeanCtorObject<1> =
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
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__0___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__0___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0_value: LeanStringObject<
    46,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        111, 110, 108, 121, 32, 111, 110, 101, 32, 98, 108, 111, 99, 107, 101, 100, 32, 105, 110,
        116, 101, 114, 101, 115, 116, 32, 115, 101, 108, 101, 99, 116, 111, 114, 32, 105, 115, 32,
        97, 108, 108, 111, 119, 101, 100, 0,
    ],
};
static mut l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__3___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__3___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Http_Body_Stream_interestSelector___lam__3___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_interestSelector___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Stream_interestSelector___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Stream_interestSelector___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Stream_interestSelector___lam__6___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Stream_interestSelector___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Stream_interestSelector___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_stream___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_stream___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_stream___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_stream___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_empty___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Std_Http_Body_empty___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_empty___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_empty___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_empty___lam__0___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Std_Http_Body_empty___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_empty___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_empty___lam__0___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_fromBytes___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_empty___lam__0___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_empty___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_empty___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_empty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_empty___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_empty___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instForInAsyncStreamChunk___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Stream_forIn___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instForInAsyncStreamChunk___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instForInAsyncStreamChunk___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instForInAsyncStreamChunk: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instForInAsyncStreamChunk___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0_value: LeanClosureObject<
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
    m_fun: l_Std_Http_Body_Stream_forIn_x27___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instForInContextAsyncStreamChunk: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instForInContextAsyncStreamChunk___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_close___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instStream___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_isClosed___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instStream___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_recvSelector as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instStream___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_tryRecvBody___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instStream___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_getKnownSize___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instStream___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Stream_setKnownSize___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instStream___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__5_value) as *mut LeanObject;
pub static l_Std_Http_Body_instStream___closed__6_value: LeanCtorObject<7> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Stream_instNextChunkAsync___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Std_Http_Body_instStream___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__6_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instStream: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__6_value) as *mut LeanObject;
pub static l_Std_Http_Body_instCoeStreamAny___closed__0_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__6_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instCoeStreamAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeStreamAny___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeStreamAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeStreamAny___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_instCoeResponseStreamAny___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__6_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instCoeResponseStreamAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeResponseStreamAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseStreamAny___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Std_Http_Body_instStream___closed__6_value) as *mut LeanObject],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1_value:
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
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeContextAsyncResponseStreamAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___closed__0_value
)
    as *mut LeanObject;
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(
    mut v_x_4129_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4129_) == 0 {
        let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
        v___x_4130_ = lean_unsigned_to_nat(0);
        return v___x_4130_;
    } else {
        let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
        v___x_4131_ = lean_unsigned_to_nat(1);
        return v___x_4131_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx___boxed(
    mut v_x_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4133_: *mut LeanObject = core::ptr::null_mut();
    v_res_4133_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorIdx(v_x_4132_);
    lean_dec_ref(v_x_4132_);
    return v_res_4133_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(
    mut v_t_4134_: *mut LeanObject,
    mut v_k_4135_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4134_) == 0 {
        let mut v_promise_4136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
        v_promise_4136_ = lean_ctor_get(v_t_4134_, 0);
        lean_inc(v_promise_4136_);
        lean_dec_ref_known(v_t_4134_, 1);
        v___x_4137_ = lean_apply_1(v_k_4135_, v_promise_4136_);
        return v___x_4137_;
    } else {
        let mut v_finished_4138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
        v_finished_4138_ = lean_ctor_get(v_t_4134_, 0);
        lean_inc_ref(v_finished_4138_);
        lean_dec_ref_known(v_t_4134_, 1);
        v___x_4139_ = lean_apply_1(v_k_4135_, v_finished_4138_);
        return v___x_4139_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(
    mut v_motive_4140_: *mut LeanObject,
    mut v_ctorIdx_4141_: *mut LeanObject,
    mut v_t_4142_: *mut LeanObject,
    mut v_h_4143_: *mut LeanObject,
    mut v_k_4144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    v___x_4145_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(
            v_t_4142_, v_k_4144_,
        );
    return v___x_4145_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___boxed(
    mut v_motive_4146_: *mut LeanObject,
    mut v_ctorIdx_4147_: *mut LeanObject,
    mut v_t_4148_: *mut LeanObject,
    mut v_h_4149_: *mut LeanObject,
    mut v_k_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4151_: *mut LeanObject = core::ptr::null_mut();
    v_res_4151_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim(
        v_motive_4146_,
        v_ctorIdx_4147_,
        v_t_4148_,
        v_h_4149_,
        v_k_4150_,
    );
    lean_dec(v_ctorIdx_4147_);
    return v_res_4151_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim___redArg(
    mut v_t_4152_: *mut LeanObject,
    mut v_normal_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    v___x_4154_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(
            v_t_4152_,
            v_normal_4153_,
        );
    return v___x_4154_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_normal_elim(
    mut v_motive_4155_: *mut LeanObject,
    mut v_t_4156_: *mut LeanObject,
    mut v_h_4157_: *mut LeanObject,
    mut v_normal_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(
            v_t_4156_,
            v_normal_4158_,
        );
    return v___x_4159_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim___redArg(
    mut v_t_4160_: *mut LeanObject,
    mut v_select_4161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(
            v_t_4160_,
            v_select_4161_,
        );
    return v___x_4162_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_select_elim(
    mut v_motive_4163_: *mut LeanObject,
    mut v_t_4164_: *mut LeanObject,
    mut v_h_4165_: *mut LeanObject,
    mut v_select_4166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    v___x_4167_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_ctorElim___redArg(
            v_t_4164_,
            v_select_4166_,
        );
    return v___x_4167_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(
    mut v_x_4168_: *mut LeanObject,
    mut v_w_4169_: *mut LeanObject,
    mut v_lose_4170_: *mut LeanObject,
) -> u8 {
    let mut v_finished_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4176_: u8 = 0;
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_4172_ = lean_ctor_get(v_w_4169_, 0);
                v_promise_4173_ = lean_ctor_get(v_w_4169_, 1);
                v___x_4174_ = lean_st_ref_take(v_finished_4172_);
                v___x_4184_ = (lean_unbox(v___x_4174_) as u8);
                lean_dec(v___x_4174_);
                if v___x_4184_ == 0 {
                    v___x_4185_ = 1;
                    v___y_4176_ = v___x_4185_;
                    state = 1;
                    continue;
                } else {
                    v___x_4186_ = 0;
                    v___y_4176_ = v___x_4186_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4177_ = 1;
                v___x_4178_ = lean_box((v___x_4177_) as usize);
                v___x_4179_ = lean_st_ref_set(v_finished_4172_, v___x_4178_);
                if v___y_4176_ == 0 {
                    lean_dec(v_x_4168_);
                    v___x_4180_ = lean_apply_1(v_lose_4170_, lean_box(0));
                    v___x_4181_ = (lean_unbox(v___x_4180_) as u8);
                    return v___x_4181_;
                } else {
                    lean_dec_ref(v_lose_4170_);
                    v___x_4182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4182_, 0, v_x_4168_);
                    v___x_4183_ = lean_io_promise_resolve(v___x_4182_, v_promise_4173_);
                    return v___y_4176_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0___boxed(
    mut v_x_4187_: *mut LeanObject,
    mut v_w_4188_: *mut LeanObject,
    mut v_lose_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4191_: u8 = 0;
    let mut v_r_4192_: *mut LeanObject = core::ptr::null_mut();
    v_res_4191_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_4187_, v_w_4188_, v_lose_4189_);
    lean_dec_ref(v_w_4188_);
    v_r_4192_ = lean_box((v_res_4191_) as usize);
    return v_r_4192_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(
    mut v___x_4193_: u8,
) -> u8 {
    return v___x_4193_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0___boxed(
    mut v___x_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390__boxed_4197_: u8 = 0;
    let mut v_res_4198_: u8 = 0;
    let mut v_r_4199_: *mut LeanObject = core::ptr::null_mut();
    v___x_390__boxed_4197_ = (lean_unbox(v___x_4195_) as u8);
    v_res_4198_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___lam__0(
            v___x_390__boxed_4197_,
        );
    v_r_4199_ = lean_box((v_res_4198_) as usize);
    return v_r_4199_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(
    mut v_c_4203_: *mut LeanObject,
    mut v_x_4204_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_c_4203_) == 0 {
        let mut v_promise_4206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4208_: u8 = 0;
        v_promise_4206_ = lean_ctor_get(v_c_4203_, 0);
        v___x_4207_ = lean_io_promise_resolve(v_x_4204_, v_promise_4206_);
        v___x_4208_ = 1;
        return v___x_4208_;
    } else {
        let mut v_finished_4209_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lose_4210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4211_: u8 = 0;
        v_finished_4209_ = lean_ctor_get(v_c_4203_, 0);
        v_lose_4210_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0;
        v___x_4211_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve_spec__0(v_x_4204_, v_finished_4209_, v_lose_4210_);
        return v___x_4211_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed(
    mut v_c_4212_: *mut LeanObject,
    mut v_x_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4215_: u8 = 0;
    let mut v_r_4216_: *mut LeanObject = core::ptr::null_mut();
    v_res_4215_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(
        v_c_4212_, v_x_4213_,
    );
    lean_dec_ref(v_c_4212_);
    v_r_4216_ = lean_box((v_res_4215_) as usize);
    return v_r_4216_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(
    mut v_x_4217_: u8,
    mut v_w_4218_: *mut LeanObject,
    mut v_lose_4219_: *mut LeanObject,
) -> u8 {
    let mut v_finished_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: u8 = 0;
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: u8 = 0;
    let mut v___x_4236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_4221_ = lean_ctor_get(v_w_4218_, 0);
                v_promise_4222_ = lean_ctor_get(v_w_4218_, 1);
                v___x_4223_ = lean_st_ref_take(v_finished_4221_);
                v___x_4234_ = (lean_unbox(v___x_4223_) as u8);
                lean_dec(v___x_4223_);
                if v___x_4234_ == 0 {
                    v___x_4235_ = 1;
                    v___y_4225_ = v___x_4235_;
                    state = 1;
                    continue;
                } else {
                    v___x_4236_ = 0;
                    v___y_4225_ = v___x_4236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4226_ = 1;
                v___x_4227_ = lean_box((v___x_4226_) as usize);
                v___x_4228_ = lean_st_ref_set(v_finished_4221_, v___x_4227_);
                if v___y_4225_ == 0 {
                    v___x_4229_ = lean_apply_1(v_lose_4219_, lean_box(0));
                    v___x_4230_ = (lean_unbox(v___x_4229_) as u8);
                    return v___x_4230_;
                } else {
                    lean_dec_ref(v_lose_4219_);
                    v___x_4231_ = lean_box((v_x_4217_) as usize);
                    v___x_4232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4232_, 0, v___x_4231_);
                    v___x_4233_ = lean_io_promise_resolve(v___x_4232_, v_promise_4222_);
                    return v___y_4225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0___boxed(
    mut v_x_4237_: *mut LeanObject,
    mut v_w_4238_: *mut LeanObject,
    mut v_lose_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4241_: u8 = 0;
    let mut v_res_4242_: u8 = 0;
    let mut v_r_4243_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4241_ = (lean_unbox(v_x_4237_) as u8);
    v_res_4242_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_boxed_4241_, v_w_4238_, v_lose_4239_);
    lean_dec_ref(v_w_4238_);
    v_r_4243_ = lean_box((v_res_4242_) as usize);
    return v_r_4243_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(
    mut v_waiter_4244_: *mut LeanObject,
    mut v_x_4245_: u8,
) -> u8 {
    let mut v_lose_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: u8 = 0;
    v_lose_4247_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___closed__0;
    v___x_4248_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter_spec__0(v_x_4245_, v_waiter_4244_, v_lose_4247_);
    return v___x_4248_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed(
    mut v_waiter_4249_: *mut LeanObject,
    mut v_x_4250_: *mut LeanObject,
    mut v_a_4251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4252_: u8 = 0;
    let mut v_res_4253_: u8 = 0;
    let mut v_r_4254_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4252_ = (lean_unbox(v_x_4250_) as u8);
    v_res_4253_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(
            v_waiter_4249_,
            v_x_boxed_4252_,
        );
    lean_dec_ref(v_waiter_4249_);
    v_r_4254_ = lean_box((v_res_4253_) as usize);
    return v_r_4254_;
}
pub unsafe fn l_Std_Http_Body_mkStream___lam__0(mut v_x_4266_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4276_: u8 = 0;
    let mut v_a_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4280_: u8 = 0;
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4266_) == 0 {
                    v_a_4268_ = lean_ctor_get(v_x_4266_, 0);
                    v_isSharedCheck_4276_ = (!lean_is_exclusive(v_x_4266_)) as u8;
                    if v_isSharedCheck_4276_ == 0 {
                        v___x_4270_ = v_x_4266_;
                        v_isShared_4271_ = v_isSharedCheck_4276_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4268_);
                        lean_dec(v_x_4266_);
                        v___x_4270_ = lean_box(0);
                        v_isShared_4271_ = v_isSharedCheck_4276_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4277_ = lean_ctor_get(v_x_4266_, 0);
                    v_isSharedCheck_4285_ = (!lean_is_exclusive(v_x_4266_)) as u8;
                    if v_isSharedCheck_4285_ == 0 {
                        v___x_4279_ = v_x_4266_;
                        v_isShared_4280_ = v_isSharedCheck_4285_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4277_);
                        lean_dec(v_x_4266_);
                        v___x_4279_ = lean_box(0);
                        v_isShared_4280_ = v_isSharedCheck_4285_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4271_ == 0 {
                    v___x_4273_ = v___x_4270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4268_);
                    v___x_4273_ = v_reuseFailAlloc_4275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4274_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4274_, 0, v___x_4273_);
                return v___x_4274_;
            }
            3 => {
                if v_isShared_4280_ == 0 {
                    v___x_4282_ = v___x_4279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4277_);
                    v___x_4282_ = v_reuseFailAlloc_4284_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4283_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4283_, 0, v___x_4282_);
                return v___x_4283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_mkStream___lam__0___boxed(
    mut v_x_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4288_: *mut LeanObject = core::ptr::null_mut();
    v_res_4288_ = l_Std_Http_Body_mkStream___lam__0(v_x_4286_);
    return v_res_4288_;
}
pub unsafe fn l_Std_Http_Body_mkStream() -> *mut LeanObject {
    let mut v___x_4294_: u8 = 0;
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    v___x_4294_ = 0;
    v___x_4295_ = l_Std_Http_Body_mkStream___closed__0;
    v___x_4296_ = l_Std_Mutex_new___redArg(v___x_4295_);
    v___f_4297_ = l_Std_Http_Body_mkStream___closed__1;
    v___x_4298_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4298_, 0, v___x_4296_);
    v___x_4299_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4299_, 0, v___x_4298_);
    v___x_4300_ = lean_unsigned_to_nat(0);
    v___x_4301_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4300_,
        v___x_4294_,
        v___x_4299_,
        v___f_4297_,
    );
    return v___x_4301_;
}
pub unsafe fn l_Std_Http_Body_mkStream___boxed(mut v_a_4302_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4303_: *mut LeanObject = core::ptr::null_mut();
    v_res_4303_ = l_Std_Http_Body_mkStream();
    return v_res_4303_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(
    mut v_knownSize_4304_: *mut LeanObject,
    mut v_chunk_4305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v_n_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v_data_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v_unused_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_knownSize_4304_) == 1 {
                    v_val_4306_ = lean_ctor_get(v_knownSize_4304_, 0);
                    lean_inc(v_val_4306_);
                    if lean_obj_tag(v_val_4306_) == 1 {
                        v_isSharedCheck_4324_ = (!lean_is_exclusive(v_knownSize_4304_)) as u8;
                        if v_isSharedCheck_4324_ == 0 {
                            v_unused_4325_ = lean_ctor_get(v_knownSize_4304_, 0);
                            lean_dec(v_unused_4325_);
                            v___x_4308_ = v_knownSize_4304_;
                            v_isShared_4309_ = v_isSharedCheck_4324_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_knownSize_4304_);
                            v___x_4308_ = lean_box(0);
                            v_isShared_4309_ = v_isSharedCheck_4324_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_4306_);
                        return v_knownSize_4304_;
                    }
                } else {
                    return v_knownSize_4304_;
                }
            }
            1 => {
                v_n_4310_ = lean_ctor_get(v_val_4306_, 0);
                v_isSharedCheck_4323_ = (!lean_is_exclusive(v_val_4306_)) as u8;
                if v_isSharedCheck_4323_ == 0 {
                    v___x_4312_ = v_val_4306_;
                    v_isShared_4313_ = v_isSharedCheck_4323_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_n_4310_);
                    lean_dec(v_val_4306_);
                    v___x_4312_ = lean_box(0);
                    v_isShared_4313_ = v_isSharedCheck_4323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_data_4314_ = lean_ctor_get(v_chunk_4305_, 0);
                v___x_4315_ = lean_byte_array_size(v_data_4314_);
                v___x_4316_ = lean_nat_sub(v_n_4310_, v___x_4315_);
                lean_dec(v_n_4310_);
                if v_isShared_4313_ == 0 {
                    lean_ctor_set(v___x_4312_, 0, v___x_4316_);
                    v___x_4318_ = v___x_4312_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4316_);
                    v___x_4318_ = v_reuseFailAlloc_4322_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4309_ == 0 {
                    lean_ctor_set(v___x_4308_, 0, v___x_4318_);
                    v___x_4320_ = v___x_4308_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4318_);
                    v___x_4320_ = v_reuseFailAlloc_4321_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize___boxed(
    mut v_knownSize_4326_: *mut LeanObject,
    mut v_chunk_4327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4328_: *mut LeanObject = core::ptr::null_mut();
    v_res_4328_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(
        v_knownSize_4326_,
        v_chunk_4327_,
    );
    lean_dec_ref(v_chunk_4327_);
    return v_res_4328_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(
    mut v_pendingProducer_4329_: *mut LeanObject,
    mut v_pendingConsumer_4330_: *mut LeanObject,
    mut v_closed_4331_: u8,
    mut v_knownSize_4332_: *mut LeanObject,
    mut v_pendingIncompleteChunk_4333_: *mut LeanObject,
    mut v_inst_4334_: *mut LeanObject,
    mut v_interestWaiter_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4337_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_4337_, 0, v_pendingProducer_4329_);
    lean_ctor_set(v___x_4337_, 1, v_pendingConsumer_4330_);
    lean_ctor_set(v___x_4337_, 2, v_interestWaiter_4335_);
    lean_ctor_set(v___x_4337_, 3, v_knownSize_4332_);
    lean_ctor_set(v___x_4337_, 4, v_pendingIncompleteChunk_4333_);
    lean_ctor_set_uint8(
        v___x_4337_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v_closed_4331_,
    );
    lean_inc(v___y_4336_);
    v___x_4338_ = lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_4338_, 0, lean_box(0));
    lean_closure_set(v___x_4338_, 1, lean_box(0));
    lean_closure_set(v___x_4338_, 2, v___y_4336_);
    lean_closure_set(v___x_4338_, 3, v___x_4337_);
    v___x_4339_ = lean_apply_2(v_inst_4334_, lean_box(0), v___x_4338_);
    return v___x_4339_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed(
    mut v_pendingProducer_4340_: *mut LeanObject,
    mut v_pendingConsumer_4341_: *mut LeanObject,
    mut v_closed_4342_: *mut LeanObject,
    mut v_knownSize_4343_: *mut LeanObject,
    mut v_pendingIncompleteChunk_4344_: *mut LeanObject,
    mut v_inst_4345_: *mut LeanObject,
    mut v_interestWaiter_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_4348_: u8 = 0;
    let mut v_res_4349_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_4348_ = (lean_unbox(v_closed_4342_) as u8);
    v_res_4349_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0(v_pendingProducer_4340_, v_pendingConsumer_4341_, v_closed_boxed_4348_, v_knownSize_4343_, v_pendingIncompleteChunk_4344_, v_inst_4345_, v_interestWaiter_4346_, v___y_4347_);
    lean_dec(v___y_4347_);
    return v_res_4349_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(
    mut v___f_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v_a_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4351_);
    v___x_4353_ = lean_apply_2(v___f_4350_, v_a_4352_, v___y_4351_);
    return v___x_4353_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed(
    mut v___f_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4357_: *mut LeanObject = core::ptr::null_mut();
    v_res_4357_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1(v___f_4354_, v___y_4355_, v_a_4356_);
    lean_dec(v___y_4355_);
    return v_res_4357_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(
    mut v_toApplicative_4358_: *mut LeanObject,
    mut v_interestWaiter_4359_: *mut LeanObject,
    mut v_toBind_4360_: *mut LeanObject,
    mut v___f_4361_: *mut LeanObject,
    mut v___f_4362_: *mut LeanObject,
    mut v_a_4363_: u8,
) -> *mut LeanObject {
    if v_a_4363_ == 0 {
        let mut v_toPure_4364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4362_);
        v_toPure_4364_ = lean_ctor_get(v_toApplicative_4358_, 1);
        lean_inc(v_toPure_4364_);
        lean_dec_ref(v_toApplicative_4358_);
        v___x_4365_ = lean_apply_2(v_toPure_4364_, lean_box(0), v_interestWaiter_4359_);
        v___x_4366_ = lean_apply_4(
            v_toBind_4360_,
            lean_box(0),
            lean_box(0),
            v___x_4365_,
            v___f_4361_,
        );
        return v___x_4366_;
    } else {
        let mut v_toPure_4367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4361_);
        lean_dec(v_interestWaiter_4359_);
        v_toPure_4367_ = lean_ctor_get(v_toApplicative_4358_, 1);
        lean_inc(v_toPure_4367_);
        lean_dec_ref(v_toApplicative_4358_);
        v___x_4368_ = lean_box(0);
        v___x_4369_ = lean_apply_2(v_toPure_4367_, lean_box(0), v___x_4368_);
        v___x_4370_ = lean_apply_4(
            v_toBind_4360_,
            lean_box(0),
            lean_box(0),
            v___x_4369_,
            v___f_4362_,
        );
        return v___x_4370_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed(
    mut v_toApplicative_4371_: *mut LeanObject,
    mut v_interestWaiter_4372_: *mut LeanObject,
    mut v_toBind_4373_: *mut LeanObject,
    mut v___f_4374_: *mut LeanObject,
    mut v___f_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4377_: u8 = 0;
    let mut v_res_4378_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4377_ = (lean_unbox(v_a_4376_) as u8);
    v_res_4378_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4(v_toApplicative_4371_, v_interestWaiter_4372_, v_toBind_4373_, v___f_4374_, v___f_4375_, v_a_boxed_4377_);
    return v_res_4378_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(
    mut v_pendingProducer_4379_: *mut LeanObject,
    mut v_closed_4380_: u8,
    mut v_knownSize_4381_: *mut LeanObject,
    mut v_pendingIncompleteChunk_4382_: *mut LeanObject,
    mut v_inst_4383_: *mut LeanObject,
    mut v_interestWaiter_4384_: *mut LeanObject,
    mut v_toApplicative_4385_: *mut LeanObject,
    mut v_toBind_4386_: *mut LeanObject,
    mut v_pendingConsumer_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4390_: *mut LeanObject = core::ptr::null_mut();
    v___x_4389_ = lean_box((v_closed_4380_) as usize);
    lean_inc(v_inst_4383_);
    v___f_4390_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 6);
    lean_closure_set(v___f_4390_, 0, v_pendingProducer_4379_);
    lean_closure_set(v___f_4390_, 1, v_pendingConsumer_4387_);
    lean_closure_set(v___f_4390_, 2, v___x_4389_);
    lean_closure_set(v___f_4390_, 3, v_knownSize_4381_);
    lean_closure_set(v___f_4390_, 4, v_pendingIncompleteChunk_4382_);
    lean_closure_set(v___f_4390_, 5, v_inst_4383_);
    if lean_obj_tag(v_interestWaiter_4384_) == 0 {
        let mut v_toPure_4391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_4383_);
        v_toPure_4391_ = lean_ctor_get(v_toApplicative_4385_, 1);
        lean_inc(v_toPure_4391_);
        lean_dec_ref(v_toApplicative_4385_);
        lean_inc(v___y_4388_);
        v___f_4392_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_4392_, 0, v___f_4390_);
        lean_closure_set(v___f_4392_, 1, v___y_4388_);
        v___x_4393_ = lean_apply_2(v_toPure_4391_, lean_box(0), v_interestWaiter_4384_);
        v___x_4394_ = lean_apply_4(
            v_toBind_4386_,
            lean_box(0),
            lean_box(0),
            v___x_4393_,
            v___f_4392_,
        );
        return v___x_4394_;
    } else {
        let mut v_val_4395_: *mut LeanObject = core::ptr::null_mut();
        let mut v_finished_4396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
        v_val_4395_ = lean_ctor_get(v_interestWaiter_4384_, 0);
        v_finished_4396_ = lean_ctor_get(v_val_4395_, 0);
        lean_inc(v_finished_4396_);
        lean_inc(v___y_4388_);
        v___f_4397_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_4397_, 0, v___f_4390_);
        lean_closure_set(v___f_4397_, 1, v___y_4388_);
        lean_inc_ref(v___f_4397_);
        lean_inc(v_toBind_4386_);
        v___f_4398_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_4398_, 0, v_toApplicative_4385_);
        lean_closure_set(v___f_4398_, 1, v_interestWaiter_4384_);
        lean_closure_set(v___f_4398_, 2, v_toBind_4386_);
        lean_closure_set(v___f_4398_, 3, v___f_4397_);
        lean_closure_set(v___f_4398_, 4, v___f_4397_);
        v___x_4399_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
        lean_closure_set(v___x_4399_, 0, lean_box(0));
        lean_closure_set(v___x_4399_, 1, lean_box(0));
        lean_closure_set(v___x_4399_, 2, v_finished_4396_);
        v___x_4400_ = lean_apply_2(v_inst_4383_, lean_box(0), v___x_4399_);
        v___x_4401_ = lean_apply_4(
            v_toBind_4386_,
            lean_box(0),
            lean_box(0),
            v___x_4400_,
            v___f_4398_,
        );
        return v___x_4401_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed(
    mut v_pendingProducer_4402_: *mut LeanObject,
    mut v_closed_4403_: *mut LeanObject,
    mut v_knownSize_4404_: *mut LeanObject,
    mut v_pendingIncompleteChunk_4405_: *mut LeanObject,
    mut v_inst_4406_: *mut LeanObject,
    mut v_interestWaiter_4407_: *mut LeanObject,
    mut v_toApplicative_4408_: *mut LeanObject,
    mut v_toBind_4409_: *mut LeanObject,
    mut v_pendingConsumer_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_4412_: u8 = 0;
    let mut v_res_4413_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_4412_ = (lean_unbox(v_closed_4403_) as u8);
    v_res_4413_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2(v_pendingProducer_4402_, v_closed_boxed_4412_, v_knownSize_4404_, v_pendingIncompleteChunk_4405_, v_inst_4406_, v_interestWaiter_4407_, v_toApplicative_4408_, v_toBind_4409_, v_pendingConsumer_4410_, v___y_4411_);
    lean_dec(v___y_4411_);
    return v_res_4413_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(
    mut v___f_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4415_);
    v___x_4417_ = lean_apply_2(v___f_4414_, v_a_4416_, v___y_4415_);
    return v___x_4417_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed(
    mut v___f_4418_: *mut LeanObject,
    mut v___y_4419_: *mut LeanObject,
    mut v_a_4420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4421_: *mut LeanObject = core::ptr::null_mut();
    v_res_4421_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3(v___f_4418_, v___y_4419_, v_a_4420_);
    lean_dec(v___y_4419_);
    return v_res_4421_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(
    mut v___f_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
    mut v_a_4424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4423_);
    v___x_4425_ = lean_apply_2(v___f_4422_, v_a_4424_, v_a_4423_);
    return v___x_4425_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed(
    mut v___f_4426_: *mut LeanObject,
    mut v_a_4427_: *mut LeanObject,
    mut v_a_4428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4429_: *mut LeanObject = core::ptr::null_mut();
    v_res_4429_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5(v___f_4426_, v_a_4427_, v_a_4428_);
    lean_dec(v_a_4427_);
    return v_res_4429_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(
    mut v_toApplicative_4430_: *mut LeanObject,
    mut v_pendingConsumer_4431_: *mut LeanObject,
    mut v_toBind_4432_: *mut LeanObject,
    mut v___f_4433_: *mut LeanObject,
    mut v___f_4434_: *mut LeanObject,
    mut v_a_4435_: u8,
) -> *mut LeanObject {
    if v_a_4435_ == 0 {
        let mut v_toPure_4436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4434_);
        v_toPure_4436_ = lean_ctor_get(v_toApplicative_4430_, 1);
        lean_inc(v_toPure_4436_);
        lean_dec_ref(v_toApplicative_4430_);
        v___x_4437_ = lean_apply_2(v_toPure_4436_, lean_box(0), v_pendingConsumer_4431_);
        v___x_4438_ = lean_apply_4(
            v_toBind_4432_,
            lean_box(0),
            lean_box(0),
            v___x_4437_,
            v___f_4433_,
        );
        return v___x_4438_;
    } else {
        let mut v_toPure_4439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_4433_);
        lean_dec(v_pendingConsumer_4431_);
        v_toPure_4439_ = lean_ctor_get(v_toApplicative_4430_, 1);
        lean_inc(v_toPure_4439_);
        lean_dec_ref(v_toApplicative_4430_);
        v___x_4440_ = lean_box(0);
        v___x_4441_ = lean_apply_2(v_toPure_4439_, lean_box(0), v___x_4440_);
        v___x_4442_ = lean_apply_4(
            v_toBind_4432_,
            lean_box(0),
            lean_box(0),
            v___x_4441_,
            v___f_4434_,
        );
        return v___x_4442_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed(
    mut v_toApplicative_4443_: *mut LeanObject,
    mut v_pendingConsumer_4444_: *mut LeanObject,
    mut v_toBind_4445_: *mut LeanObject,
    mut v___f_4446_: *mut LeanObject,
    mut v___f_4447_: *mut LeanObject,
    mut v_a_4448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4449_: u8 = 0;
    let mut v_res_4450_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4449_ = (lean_unbox(v_a_4448_) as u8);
    v_res_4450_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7(v_toApplicative_4443_, v_pendingConsumer_4444_, v_toBind_4445_, v___f_4446_, v___f_4447_, v_a_boxed_4449_);
    return v_res_4450_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(
    mut v_inst_4451_: *mut LeanObject,
    mut v_toApplicative_4452_: *mut LeanObject,
    mut v_toBind_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
    mut v_a_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pendingProducer_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_4459_: u8 = 0;
    let mut v_knownSize_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pendingProducer_4456_ = lean_ctor_get(v_a_4455_, 0);
                lean_inc(v_pendingProducer_4456_);
                v_pendingConsumer_4457_ = lean_ctor_get(v_a_4455_, 1);
                lean_inc(v_pendingConsumer_4457_);
                v_interestWaiter_4458_ = lean_ctor_get(v_a_4455_, 2);
                lean_inc(v_interestWaiter_4458_);
                v_closed_4459_ = lean_ctor_get_uint8(
                    v_a_4455_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_knownSize_4460_ = lean_ctor_get(v_a_4455_, 3);
                lean_inc(v_knownSize_4460_);
                v_pendingIncompleteChunk_4461_ = lean_ctor_get(v_a_4455_, 4);
                lean_inc(v_pendingIncompleteChunk_4461_);
                lean_dec_ref(v_a_4455_);
                v___x_4462_ = lean_box((v_closed_4459_) as usize);
                lean_inc(v_toBind_4453_);
                lean_inc_ref(v_toApplicative_4452_);
                lean_inc(v_inst_4451_);
                v___f_4463_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 8);
                lean_closure_set(v___f_4463_, 0, v_pendingProducer_4456_);
                lean_closure_set(v___f_4463_, 1, v___x_4462_);
                lean_closure_set(v___f_4463_, 2, v_knownSize_4460_);
                lean_closure_set(v___f_4463_, 3, v_pendingIncompleteChunk_4461_);
                lean_closure_set(v___f_4463_, 4, v_inst_4451_);
                lean_closure_set(v___f_4463_, 5, v_interestWaiter_4458_);
                lean_closure_set(v___f_4463_, 6, v_toApplicative_4452_);
                lean_closure_set(v___f_4463_, 7, v_toBind_4453_);
                if lean_obj_tag(v_pendingConsumer_4457_) == 1 {
                    v_val_4470_ = lean_ctor_get(v_pendingConsumer_4457_, 0);
                    if lean_obj_tag(v_val_4470_) == 1 {
                        v_finished_4471_ = lean_ctor_get(v_val_4470_, 0);
                        v_finished_4472_ = lean_ctor_get(v_finished_4471_, 0);
                        lean_inc(v_finished_4472_);
                        lean_inc(v_a_4454_);
                        v___f_4473_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__5___boxed as *mut core::ffi::c_void, 3, 2);
                        lean_closure_set(v___f_4473_, 0, v___f_4463_);
                        lean_closure_set(v___f_4473_, 1, v_a_4454_);
                        lean_inc_ref(v___f_4473_);
                        lean_inc(v_toBind_4453_);
                        v___f_4474_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 5);
                        lean_closure_set(v___f_4474_, 0, v_toApplicative_4452_);
                        lean_closure_set(v___f_4474_, 1, v_pendingConsumer_4457_);
                        lean_closure_set(v___f_4474_, 2, v_toBind_4453_);
                        lean_closure_set(v___f_4474_, 3, v___f_4473_);
                        lean_closure_set(v___f_4474_, 4, v___f_4473_);
                        v___x_4475_ = lean_alloc_closure(
                            l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        lean_closure_set(v___x_4475_, 0, lean_box(0));
                        lean_closure_set(v___x_4475_, 1, lean_box(0));
                        lean_closure_set(v___x_4475_, 2, v_finished_4472_);
                        v___x_4476_ = lean_apply_2(v_inst_4451_, lean_box(0), v___x_4475_);
                        v___x_4477_ = lean_apply_4(
                            v_toBind_4453_,
                            lean_box(0),
                            lean_box(0),
                            v___x_4476_,
                            v___f_4474_,
                        );
                        return v___x_4477_;
                    } else {
                        lean_dec(v_inst_4451_);
                        v___y_4465_ = v_a_4454_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_inst_4451_);
                    v___y_4465_ = v_a_4454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_4466_ = lean_ctor_get(v_toApplicative_4452_, 1);
                lean_inc(v_toPure_4466_);
                lean_dec_ref(v_toApplicative_4452_);
                lean_inc(v___y_4465_);
                v___f_4467_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_4467_, 0, v___f_4463_);
                lean_closure_set(v___f_4467_, 1, v___y_4465_);
                v___x_4468_ = lean_apply_2(v_toPure_4466_, lean_box(0), v_pendingConsumer_4457_);
                v___x_4469_ = lean_apply_4(
                    v_toBind_4453_,
                    lean_box(0),
                    lean_box(0),
                    v___x_4468_,
                    v___f_4467_,
                );
                return v___x_4469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed(
    mut v_inst_4478_: *mut LeanObject,
    mut v_toApplicative_4479_: *mut LeanObject,
    mut v_toBind_4480_: *mut LeanObject,
    mut v_a_4481_: *mut LeanObject,
    mut v_a_4482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4483_: *mut LeanObject = core::ptr::null_mut();
    v_res_4483_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6(v_inst_4478_, v_toApplicative_4479_, v_toBind_4480_, v_a_4481_, v_a_4482_);
    lean_dec(v_a_4481_);
    return v_res_4483_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(
    mut v_inst_4484_: *mut LeanObject,
    mut v_inst_4485_: *mut LeanObject,
    mut v_a_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4487_ = lean_ctor_get(v_inst_4484_, 0);
    lean_inc_ref(v_toApplicative_4487_);
    v_toBind_4488_ = lean_ctor_get(v_inst_4484_, 1);
    lean_inc_n(v_toBind_4488_, 2);
    lean_dec_ref(v_inst_4484_);
    lean_inc_n(v_a_4486_, 2);
    lean_inc(v_inst_4485_);
    v___f_4489_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___lam__6___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___f_4489_, 0, v_inst_4485_);
    lean_closure_set(v___f_4489_, 1, v_toApplicative_4487_);
    lean_closure_set(v___f_4489_, 2, v_toBind_4488_);
    lean_closure_set(v___f_4489_, 3, v_a_4486_);
    v___x_4490_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4490_, 0, lean_box(0));
    lean_closure_set(v___x_4490_, 1, lean_box(0));
    lean_closure_set(v___x_4490_, 2, v_a_4486_);
    v___x_4491_ = lean_apply_2(v_inst_4485_, lean_box(0), v___x_4490_);
    v___x_4492_ = lean_apply_4(
        v_toBind_4488_,
        lean_box(0),
        lean_box(0),
        v___x_4491_,
        v___f_4489_,
    );
    return v___x_4492_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg___boxed(
    mut v_inst_4493_: *mut LeanObject,
    mut v_inst_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4496_: *mut LeanObject = core::ptr::null_mut();
    v_res_4496_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_4493_, v_inst_4494_, v_a_4495_);
    lean_dec(v_a_4495_);
    return v_res_4496_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(
    mut v_m_4497_: *mut LeanObject,
    mut v_inst_4498_: *mut LeanObject,
    mut v_inst_4499_: *mut LeanObject,
    mut v_a_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    v___x_4501_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___redArg(v_inst_4498_, v_inst_4499_, v_a_4500_);
    return v___x_4501_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___boxed(
    mut v_m_4502_: *mut LeanObject,
    mut v_inst_4503_: *mut LeanObject,
    mut v_inst_4504_: *mut LeanObject,
    mut v_a_4505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4506_: *mut LeanObject = core::ptr::null_mut();
    v_res_4506_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters(
            v_m_4502_,
            v_inst_4503_,
            v_inst_4504_,
            v_a_4505_,
        );
    lean_dec(v_a_4505_);
    return v_res_4506_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(
    mut v_pendingProducer_4507_: *mut LeanObject,
    mut v_pendingConsumer_4508_: *mut LeanObject,
    mut v_closed_4509_: u8,
    mut v_knownSize_4510_: *mut LeanObject,
    mut v_pendingIncompleteChunk_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_inst_4513_: *mut LeanObject,
    mut v_a_4514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    v___x_4515_ = lean_box(0);
    v___x_4516_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_4516_, 0, v_pendingProducer_4507_);
    lean_ctor_set(v___x_4516_, 1, v_pendingConsumer_4508_);
    lean_ctor_set(v___x_4516_, 2, v___x_4515_);
    lean_ctor_set(v___x_4516_, 3, v_knownSize_4510_);
    lean_ctor_set(v___x_4516_, 4, v_pendingIncompleteChunk_4511_);
    lean_ctor_set_uint8(
        v___x_4516_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v_closed_4509_,
    );
    lean_inc(v_a_4512_);
    v___x_4517_ = lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_4517_, 0, lean_box(0));
    lean_closure_set(v___x_4517_, 1, lean_box(0));
    lean_closure_set(v___x_4517_, 2, v_a_4512_);
    lean_closure_set(v___x_4517_, 3, v___x_4516_);
    v___x_4518_ = lean_apply_2(v_inst_4513_, lean_box(0), v___x_4517_);
    return v___x_4518_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed(
    mut v_pendingProducer_4519_: *mut LeanObject,
    mut v_pendingConsumer_4520_: *mut LeanObject,
    mut v_closed_4521_: *mut LeanObject,
    mut v_knownSize_4522_: *mut LeanObject,
    mut v_pendingIncompleteChunk_4523_: *mut LeanObject,
    mut v_a_4524_: *mut LeanObject,
    mut v_inst_4525_: *mut LeanObject,
    mut v_a_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_4527_: u8 = 0;
    let mut v_res_4528_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_4527_ = (lean_unbox(v_closed_4521_) as u8);
    v_res_4528_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0(v_pendingProducer_4519_, v_pendingConsumer_4520_, v_closed_boxed_4527_, v_knownSize_4522_, v_pendingIncompleteChunk_4523_, v_a_4524_, v_inst_4525_, v_a_4526_);
    lean_dec(v_a_4524_);
    return v_res_4528_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(
    mut v_toApplicative_4529_: *mut LeanObject,
    mut v_a_4530_: *mut LeanObject,
    mut v_inst_4531_: *mut LeanObject,
    mut v_inst_4532_: *mut LeanObject,
    mut v_toBind_4533_: *mut LeanObject,
    mut v_a_4534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_interestWaiter_4535_: *mut LeanObject = core::ptr::null_mut();
    v_interestWaiter_4535_ = lean_ctor_get(v_a_4534_, 2);
    lean_inc(v_interestWaiter_4535_);
    if lean_obj_tag(v_interestWaiter_4535_) == 1 {
        let mut v_toFunctor_4536_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pendingProducer_4537_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pendingConsumer_4538_: *mut LeanObject = core::ptr::null_mut();
        let mut v_closed_4539_: u8 = 0;
        let mut v_knownSize_4540_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pendingIncompleteChunk_4541_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_4542_: *mut LeanObject = core::ptr::null_mut();
        let mut v_mapConst_4543_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4545_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4546_: u8 = 0;
        let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_4536_ = lean_ctor_get(v_toApplicative_4529_, 0);
        lean_inc_ref(v_toFunctor_4536_);
        lean_dec_ref(v_toApplicative_4529_);
        v_pendingProducer_4537_ = lean_ctor_get(v_a_4534_, 0);
        lean_inc(v_pendingProducer_4537_);
        v_pendingConsumer_4538_ = lean_ctor_get(v_a_4534_, 1);
        lean_inc(v_pendingConsumer_4538_);
        v_closed_4539_ = lean_ctor_get_uint8(
            v_a_4534_,
            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        );
        v_knownSize_4540_ = lean_ctor_get(v_a_4534_, 3);
        lean_inc(v_knownSize_4540_);
        v_pendingIncompleteChunk_4541_ = lean_ctor_get(v_a_4534_, 4);
        lean_inc(v_pendingIncompleteChunk_4541_);
        lean_dec_ref(v_a_4534_);
        v_val_4542_ = lean_ctor_get(v_interestWaiter_4535_, 0);
        lean_inc(v_val_4542_);
        lean_dec_ref_known(v_interestWaiter_4535_, 1);
        v_mapConst_4543_ = lean_ctor_get(v_toFunctor_4536_, 1);
        lean_inc(v_mapConst_4543_);
        lean_dec_ref(v_toFunctor_4536_);
        v___x_4544_ = lean_box((v_closed_4539_) as usize);
        lean_inc(v_a_4530_);
        v___f_4545_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        lean_closure_set(v___f_4545_, 0, v_pendingProducer_4537_);
        lean_closure_set(v___f_4545_, 1, v_pendingConsumer_4538_);
        lean_closure_set(v___f_4545_, 2, v___x_4544_);
        lean_closure_set(v___f_4545_, 3, v_knownSize_4540_);
        lean_closure_set(v___f_4545_, 4, v_pendingIncompleteChunk_4541_);
        lean_closure_set(v___f_4545_, 5, v_a_4530_);
        lean_closure_set(v___f_4545_, 6, v_inst_4531_);
        v___x_4546_ = 1;
        v___x_4547_ = lean_box((v___x_4546_) as usize);
        v___x_4548_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___x_4548_, 0, v_val_4542_);
        lean_closure_set(v___x_4548_, 1, v___x_4547_);
        v___x_4549_ = lean_apply_2(v_inst_4532_, lean_box(0), v___x_4548_);
        v___x_4550_ = lean_box(0);
        v___x_4551_ = lean_apply_4(
            v_mapConst_4543_,
            lean_box(0),
            lean_box(0),
            v___x_4550_,
            v___x_4549_,
        );
        v___x_4552_ = lean_apply_4(
            v_toBind_4533_,
            lean_box(0),
            lean_box(0),
            v___x_4551_,
            v___f_4545_,
        );
        return v___x_4552_;
    } else {
        let mut v_toPure_4553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_interestWaiter_4535_);
        lean_dec_ref(v_a_4534_);
        lean_dec(v_toBind_4533_);
        lean_dec(v_inst_4532_);
        lean_dec(v_inst_4531_);
        v_toPure_4553_ = lean_ctor_get(v_toApplicative_4529_, 1);
        lean_inc(v_toPure_4553_);
        lean_dec_ref(v_toApplicative_4529_);
        v___x_4554_ = lean_box(0);
        v___x_4555_ = lean_apply_2(v_toPure_4553_, lean_box(0), v___x_4554_);
        return v___x_4555_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed(
    mut v_toApplicative_4556_: *mut LeanObject,
    mut v_a_4557_: *mut LeanObject,
    mut v_inst_4558_: *mut LeanObject,
    mut v_inst_4559_: *mut LeanObject,
    mut v_toBind_4560_: *mut LeanObject,
    mut v_a_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4562_: *mut LeanObject = core::ptr::null_mut();
    v_res_4562_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1(v_toApplicative_4556_, v_a_4557_, v_inst_4558_, v_inst_4559_, v_toBind_4560_, v_a_4561_);
    lean_dec(v_a_4557_);
    return v_res_4562_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(
    mut v_inst_4563_: *mut LeanObject,
    mut v_inst_4564_: *mut LeanObject,
    mut v_inst_4565_: *mut LeanObject,
    mut v_a_4566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4567_ = lean_ctor_get(v_inst_4563_, 0);
    lean_inc_ref(v_toApplicative_4567_);
    v_toBind_4568_ = lean_ctor_get(v_inst_4563_, 1);
    lean_inc_n(v_toBind_4568_, 2);
    lean_dec_ref(v_inst_4563_);
    lean_inc(v_inst_4564_);
    lean_inc_n(v_a_4566_, 2);
    v___f_4569_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_4569_, 0, v_toApplicative_4567_);
    lean_closure_set(v___f_4569_, 1, v_a_4566_);
    lean_closure_set(v___f_4569_, 2, v_inst_4564_);
    lean_closure_set(v___f_4569_, 3, v_inst_4565_);
    lean_closure_set(v___f_4569_, 4, v_toBind_4568_);
    v___x_4570_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4570_, 0, lean_box(0));
    lean_closure_set(v___x_4570_, 1, lean_box(0));
    lean_closure_set(v___x_4570_, 2, v_a_4566_);
    v___x_4571_ = lean_apply_2(v_inst_4564_, lean_box(0), v___x_4570_);
    v___x_4572_ = lean_apply_4(
        v_toBind_4568_,
        lean_box(0),
        lean_box(0),
        v___x_4571_,
        v___f_4569_,
    );
    return v___x_4572_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg___boxed(
    mut v_inst_4573_: *mut LeanObject,
    mut v_inst_4574_: *mut LeanObject,
    mut v_inst_4575_: *mut LeanObject,
    mut v_a_4576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4577_: *mut LeanObject = core::ptr::null_mut();
    v_res_4577_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(
            v_inst_4573_,
            v_inst_4574_,
            v_inst_4575_,
            v_a_4576_,
        );
    lean_dec(v_a_4576_);
    return v_res_4577_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(
    mut v_m_4578_: *mut LeanObject,
    mut v_inst_4579_: *mut LeanObject,
    mut v_inst_4580_: *mut LeanObject,
    mut v_inst_4581_: *mut LeanObject,
    mut v_a_4582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    v___x_4583_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___redArg(
            v_inst_4579_,
            v_inst_4580_,
            v_inst_4581_,
            v_a_4582_,
        );
    return v___x_4583_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___boxed(
    mut v_m_4584_: *mut LeanObject,
    mut v_inst_4585_: *mut LeanObject,
    mut v_inst_4586_: *mut LeanObject,
    mut v_inst_4587_: *mut LeanObject,
    mut v_a_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4589_: *mut LeanObject = core::ptr::null_mut();
    v_res_4589_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest(
        v_m_4584_,
        v_inst_4585_,
        v_inst_4586_,
        v_inst_4587_,
        v_a_4588_,
    );
    lean_dec(v_a_4588_);
    return v_res_4589_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(
    mut v_toApplicative_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4593_: u8 = 0;
    let mut v_toPure_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_4598_: u8 = 0;
    let mut v___x_4599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pendingProducer_4597_ = lean_ctor_get(v_a_4591_, 0);
                if lean_obj_tag(v_pendingProducer_4597_) == 0 {
                    v_closed_4598_ = lean_ctor_get_uint8(
                        v_a_4591_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v___y_4593_ = v_closed_4598_;
                    state = 1;
                    continue;
                } else {
                    v___x_4599_ = 1;
                    v___y_4593_ = v___x_4599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_4594_ = lean_ctor_get(v_toApplicative_4590_, 1);
                lean_inc(v_toPure_4594_);
                lean_dec_ref(v_toApplicative_4590_);
                v___x_4595_ = lean_box((v___y_4593_) as usize);
                v___x_4596_ = lean_apply_2(v_toPure_4594_, lean_box(0), v___x_4595_);
                return v___x_4596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed(
    mut v_toApplicative_4600_: *mut LeanObject,
    mut v_a_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4602_: *mut LeanObject = core::ptr::null_mut();
    v_res_4602_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0(v_toApplicative_4600_, v_a_4601_);
    lean_dec_ref(v_a_4601_);
    return v_res_4602_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(
    mut v_inst_4603_: *mut LeanObject,
    mut v_inst_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4606_ = lean_ctor_get(v_inst_4603_, 0);
    lean_inc_ref(v_toApplicative_4606_);
    v_toBind_4607_ = lean_ctor_get(v_inst_4603_, 1);
    lean_inc(v_toBind_4607_);
    lean_dec_ref(v_inst_4603_);
    v___f_4608_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_4608_, 0, v_toApplicative_4606_);
    lean_inc(v_a_4605_);
    v___x_4609_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4609_, 0, lean_box(0));
    lean_closure_set(v___x_4609_, 1, lean_box(0));
    lean_closure_set(v___x_4609_, 2, v_a_4605_);
    v___x_4610_ = lean_apply_2(v_inst_4604_, lean_box(0), v___x_4609_);
    v___x_4611_ = lean_apply_4(
        v_toBind_4607_,
        lean_box(0),
        lean_box(0),
        v___x_4610_,
        v___f_4608_,
    );
    return v___x_4611_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg___boxed(
    mut v_inst_4612_: *mut LeanObject,
    mut v_inst_4613_: *mut LeanObject,
    mut v_a_4614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4615_: *mut LeanObject = core::ptr::null_mut();
    v_res_4615_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(
            v_inst_4612_,
            v_inst_4613_,
            v_a_4614_,
        );
    lean_dec(v_a_4614_);
    return v_res_4615_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(
    mut v_m_4616_: *mut LeanObject,
    mut v_inst_4617_: *mut LeanObject,
    mut v_inst_4618_: *mut LeanObject,
    mut v_a_4619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    v___x_4620_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___redArg(
            v_inst_4617_,
            v_inst_4618_,
            v_a_4619_,
        );
    return v___x_4620_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___boxed(
    mut v_m_4621_: *mut LeanObject,
    mut v_inst_4622_: *mut LeanObject,
    mut v_inst_4623_: *mut LeanObject,
    mut v_a_4624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4625_: *mut LeanObject = core::ptr::null_mut();
    v_res_4625_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27(
        v_m_4621_,
        v_inst_4622_,
        v_inst_4623_,
        v_a_4624_,
    );
    lean_dec(v_a_4624_);
    return v_res_4625_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(
    mut v_toApplicative_4626_: *mut LeanObject,
    mut v_a_4627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4629_: u8 = 0;
    let mut v_toPure_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pendingConsumer_4633_ = lean_ctor_get(v_a_4627_, 1);
                if lean_obj_tag(v_pendingConsumer_4633_) == 0 {
                    v___x_4634_ = 0;
                    v___y_4629_ = v___x_4634_;
                    state = 1;
                    continue;
                } else {
                    v___x_4635_ = 1;
                    v___y_4629_ = v___x_4635_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_4630_ = lean_ctor_get(v_toApplicative_4626_, 1);
                lean_inc(v_toPure_4630_);
                lean_dec_ref(v_toApplicative_4626_);
                v___x_4631_ = lean_box((v___y_4629_) as usize);
                v___x_4632_ = lean_apply_2(v_toPure_4630_, lean_box(0), v___x_4631_);
                return v___x_4632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed(
    mut v_toApplicative_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4638_: *mut LeanObject = core::ptr::null_mut();
    v_res_4638_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0(v_toApplicative_4636_, v_a_4637_);
    lean_dec_ref(v_a_4637_);
    return v_res_4638_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(
    mut v_inst_4639_: *mut LeanObject,
    mut v_inst_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4642_ = lean_ctor_get(v_inst_4639_, 0);
    lean_inc_ref(v_toApplicative_4642_);
    v_toBind_4643_ = lean_ctor_get(v_inst_4639_, 1);
    lean_inc(v_toBind_4643_);
    lean_dec_ref(v_inst_4639_);
    v___f_4644_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_4644_, 0, v_toApplicative_4642_);
    lean_inc(v_a_4641_);
    v___x_4645_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4645_, 0, lean_box(0));
    lean_closure_set(v___x_4645_, 1, lean_box(0));
    lean_closure_set(v___x_4645_, 2, v_a_4641_);
    v___x_4646_ = lean_apply_2(v_inst_4640_, lean_box(0), v___x_4645_);
    v___x_4647_ = lean_apply_4(
        v_toBind_4643_,
        lean_box(0),
        lean_box(0),
        v___x_4646_,
        v___f_4644_,
    );
    return v___x_4647_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg___boxed(
    mut v_inst_4648_: *mut LeanObject,
    mut v_inst_4649_: *mut LeanObject,
    mut v_a_4650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4651_: *mut LeanObject = core::ptr::null_mut();
    v_res_4651_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(
            v_inst_4648_,
            v_inst_4649_,
            v_a_4650_,
        );
    lean_dec(v_a_4650_);
    return v_res_4651_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(
    mut v_m_4652_: *mut LeanObject,
    mut v_inst_4653_: *mut LeanObject,
    mut v_inst_4654_: *mut LeanObject,
    mut v_a_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    v___x_4656_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___redArg(
            v_inst_4653_,
            v_inst_4654_,
            v_a_4655_,
        );
    return v___x_4656_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___boxed(
    mut v_m_4657_: *mut LeanObject,
    mut v_inst_4658_: *mut LeanObject,
    mut v_inst_4659_: *mut LeanObject,
    mut v_a_4660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4661_: *mut LeanObject = core::ptr::null_mut();
    v_res_4661_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27(
        v_m_4657_,
        v_inst_4658_,
        v_inst_4659_,
        v_a_4660_,
    );
    lean_dec(v_a_4660_);
    return v_res_4661_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0(
    mut v_toApplicative_4662_: *mut LeanObject,
    mut v_chunk_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_4665_ = lean_ctor_get(v_toApplicative_4662_, 1);
    lean_inc(v_toPure_4665_);
    lean_dec_ref(v_toApplicative_4662_);
    v___x_4666_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4666_, 0, v_chunk_4663_);
    v___x_4667_ = lean_apply_2(v_toPure_4665_, lean_box(0), v___x_4666_);
    return v___x_4667_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1(
    mut v_toApplicative_4668_: *mut LeanObject,
    mut v_done_4669_: *mut LeanObject,
    mut v_inst_4670_: *mut LeanObject,
    mut v_toBind_4671_: *mut LeanObject,
    mut v___f_4672_: *mut LeanObject,
    mut v_a_4673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toFunctor_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: u8 = 0;
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    v_toFunctor_4674_ = lean_ctor_get(v_toApplicative_4668_, 0);
    lean_inc_ref(v_toFunctor_4674_);
    lean_dec_ref(v_toApplicative_4668_);
    v_mapConst_4675_ = lean_ctor_get(v_toFunctor_4674_, 1);
    lean_inc(v_mapConst_4675_);
    lean_dec_ref(v_toFunctor_4674_);
    v___x_4676_ = 1;
    v___x_4677_ = lean_box((v___x_4676_) as usize);
    v___x_4678_ = lean_alloc_closure(l_IO_Promise_resolve___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4678_, 0, lean_box(0));
    lean_closure_set(v___x_4678_, 1, v___x_4677_);
    lean_closure_set(v___x_4678_, 2, v_done_4669_);
    v___x_4679_ = lean_apply_2(v_inst_4670_, lean_box(0), v___x_4678_);
    v___x_4680_ = lean_box(0);
    v___x_4681_ = lean_apply_4(
        v_mapConst_4675_,
        lean_box(0),
        lean_box(0),
        v___x_4680_,
        v___x_4679_,
    );
    v___x_4682_ = lean_apply_4(
        v_toBind_4671_,
        lean_box(0),
        lean_box(0),
        v___x_4681_,
        v___f_4672_,
    );
    return v___x_4682_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(
    mut v_toApplicative_4683_: *mut LeanObject,
    mut v_inst_4684_: *mut LeanObject,
    mut v_toBind_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
    mut v_inst_4687_: *mut LeanObject,
    mut v_a_4688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pendingProducer_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_4693_: u8 = 0;
    let mut v_knownSize_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v_chunk_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4711_: u8 = 0;
    let mut v_unused_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pendingProducer_4689_ = lean_ctor_get(v_a_4688_, 0);
                if lean_obj_tag(v_pendingProducer_4689_) == 1 {
                    v_val_4690_ = lean_ctor_get(v_pendingProducer_4689_, 0);
                    lean_inc(v_val_4690_);
                    v_pendingConsumer_4691_ = lean_ctor_get(v_a_4688_, 1);
                    v_interestWaiter_4692_ = lean_ctor_get(v_a_4688_, 2);
                    v_closed_4693_ = lean_ctor_get_uint8(
                        v_a_4688_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_knownSize_4694_ = lean_ctor_get(v_a_4688_, 3);
                    v_pendingIncompleteChunk_4695_ = lean_ctor_get(v_a_4688_, 4);
                    v_isSharedCheck_4711_ = (!lean_is_exclusive(v_a_4688_)) as u8;
                    if v_isSharedCheck_4711_ == 0 {
                        v_unused_4712_ = lean_ctor_get(v_a_4688_, 0);
                        lean_dec(v_unused_4712_);
                        v___x_4697_ = v_a_4688_;
                        v_isShared_4698_ = v_isSharedCheck_4711_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_pendingIncompleteChunk_4695_);
                        lean_inc(v_knownSize_4694_);
                        lean_inc(v_interestWaiter_4692_);
                        lean_inc(v_pendingConsumer_4691_);
                        lean_dec(v_a_4688_);
                        v___x_4697_ = lean_box(0);
                        v_isShared_4698_ = v_isSharedCheck_4711_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4688_);
                    lean_dec(v_inst_4687_);
                    lean_dec(v_toBind_4685_);
                    lean_dec(v_inst_4684_);
                    v_toPure_4713_ = lean_ctor_get(v_toApplicative_4683_, 1);
                    lean_inc(v_toPure_4713_);
                    lean_dec_ref(v_toApplicative_4683_);
                    v___x_4714_ = lean_box(0);
                    v___x_4715_ = lean_apply_2(v_toPure_4713_, lean_box(0), v___x_4714_);
                    return v___x_4715_;
                }
            }
            1 => {
                v_chunk_4699_ = lean_ctor_get(v_val_4690_, 0);
                lean_inc_ref_n(v_chunk_4699_, 2);
                v_done_4700_ = lean_ctor_get(v_val_4690_, 1);
                lean_inc(v_done_4700_);
                lean_dec(v_val_4690_);
                v___x_4701_ = lean_box(0);
                lean_inc_ref(v_toApplicative_4683_);
                v___f_4702_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_4702_, 0, v_toApplicative_4683_);
                lean_closure_set(v___f_4702_, 1, v_chunk_4699_);
                lean_inc(v_toBind_4685_);
                v___f_4703_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___f_4703_, 0, v_toApplicative_4683_);
                lean_closure_set(v___f_4703_, 1, v_done_4700_);
                lean_closure_set(v___f_4703_, 2, v_inst_4684_);
                lean_closure_set(v___f_4703_, 3, v_toBind_4685_);
                lean_closure_set(v___f_4703_, 4, v___f_4702_);
                v___x_4704_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_4694_, v_chunk_4699_);
                lean_dec_ref(v_chunk_4699_);
                if v_isShared_4698_ == 0 {
                    lean_ctor_set(v___x_4697_, 3, v___x_4704_);
                    lean_ctor_set(v___x_4697_, 0, v___x_4701_);
                    v___x_4706_ = v___x_4697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4701_);
                    lean_ctor_set(v_reuseFailAlloc_4710_, 1, v_pendingConsumer_4691_);
                    lean_ctor_set(v_reuseFailAlloc_4710_, 2, v_interestWaiter_4692_);
                    lean_ctor_set(v_reuseFailAlloc_4710_, 3, v___x_4704_);
                    lean_ctor_set(v_reuseFailAlloc_4710_, 4, v_pendingIncompleteChunk_4695_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4710_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_4693_,
                    );
                    v___x_4706_ = v_reuseFailAlloc_4710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_a_4686_);
                v___x_4707_ =
                    lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_4707_, 0, lean_box(0));
                lean_closure_set(v___x_4707_, 1, lean_box(0));
                lean_closure_set(v___x_4707_, 2, v_a_4686_);
                lean_closure_set(v___x_4707_, 3, v___x_4706_);
                v___x_4708_ = lean_apply_2(v_inst_4687_, lean_box(0), v___x_4707_);
                v___x_4709_ = lean_apply_4(
                    v_toBind_4685_,
                    lean_box(0),
                    lean_box(0),
                    v___x_4708_,
                    v___f_4703_,
                );
                return v___x_4709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed(
    mut v_toApplicative_4716_: *mut LeanObject,
    mut v_inst_4717_: *mut LeanObject,
    mut v_toBind_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_inst_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4722_: *mut LeanObject = core::ptr::null_mut();
    v_res_4722_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2(v_toApplicative_4716_, v_inst_4717_, v_toBind_4718_, v_a_4719_, v_inst_4720_, v_a_4721_);
    lean_dec(v_a_4719_);
    return v_res_4722_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(
    mut v_inst_4723_: *mut LeanObject,
    mut v_inst_4724_: *mut LeanObject,
    mut v_inst_4725_: *mut LeanObject,
    mut v_a_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4727_ = lean_ctor_get(v_inst_4723_, 0);
    lean_inc_ref(v_toApplicative_4727_);
    v_toBind_4728_ = lean_ctor_get(v_inst_4723_, 1);
    lean_inc_n(v_toBind_4728_, 2);
    lean_dec_ref(v_inst_4723_);
    lean_inc(v_inst_4724_);
    lean_inc_n(v_a_4726_, 2);
    v___f_4729_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_4729_, 0, v_toApplicative_4727_);
    lean_closure_set(v___f_4729_, 1, v_inst_4725_);
    lean_closure_set(v___f_4729_, 2, v_toBind_4728_);
    lean_closure_set(v___f_4729_, 3, v_a_4726_);
    lean_closure_set(v___f_4729_, 4, v_inst_4724_);
    v___x_4730_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4730_, 0, lean_box(0));
    lean_closure_set(v___x_4730_, 1, lean_box(0));
    lean_closure_set(v___x_4730_, 2, v_a_4726_);
    v___x_4731_ = lean_apply_2(v_inst_4724_, lean_box(0), v___x_4730_);
    v___x_4732_ = lean_apply_4(
        v_toBind_4728_,
        lean_box(0),
        lean_box(0),
        v___x_4731_,
        v___f_4729_,
    );
    return v___x_4732_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg___boxed(
    mut v_inst_4733_: *mut LeanObject,
    mut v_inst_4734_: *mut LeanObject,
    mut v_inst_4735_: *mut LeanObject,
    mut v_a_4736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4737_: *mut LeanObject = core::ptr::null_mut();
    v_res_4737_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(
            v_inst_4733_,
            v_inst_4734_,
            v_inst_4735_,
            v_a_4736_,
        );
    lean_dec(v_a_4736_);
    return v_res_4737_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(
    mut v_m_4738_: *mut LeanObject,
    mut v_inst_4739_: *mut LeanObject,
    mut v_inst_4740_: *mut LeanObject,
    mut v_inst_4741_: *mut LeanObject,
    mut v_a_4742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    v___x_4743_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___redArg(
            v_inst_4739_,
            v_inst_4740_,
            v_inst_4741_,
            v_a_4742_,
        );
    return v___x_4743_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___boxed(
    mut v_m_4744_: *mut LeanObject,
    mut v_inst_4745_: *mut LeanObject,
    mut v_inst_4746_: *mut LeanObject,
    mut v_inst_4747_: *mut LeanObject,
    mut v_a_4748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4749_: *mut LeanObject = core::ptr::null_mut();
    v_res_4749_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27(
        v_m_4744_,
        v_inst_4745_,
        v_inst_4746_,
        v_inst_4747_,
        v_a_4748_,
    );
    lean_dec(v_a_4748_);
    return v_res_4749_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(
    mut v___x_4750_: u8,
    mut v_knownSize_4751_: *mut LeanObject,
    mut v_inst_4752_: *mut LeanObject,
    mut v_____r_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    v___x_4755_ = lean_box(0);
    v___x_4756_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_4756_, 0, v___x_4755_);
    lean_ctor_set(v___x_4756_, 1, v___x_4755_);
    lean_ctor_set(v___x_4756_, 2, v___x_4755_);
    lean_ctor_set(v___x_4756_, 3, v_knownSize_4751_);
    lean_ctor_set(v___x_4756_, 4, v___x_4755_);
    lean_ctor_set_uint8(
        v___x_4756_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_4750_,
    );
    lean_inc(v___y_4754_);
    v___x_4757_ = lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_4757_, 0, lean_box(0));
    lean_closure_set(v___x_4757_, 1, lean_box(0));
    lean_closure_set(v___x_4757_, 2, v___y_4754_);
    lean_closure_set(v___x_4757_, 3, v___x_4756_);
    v___x_4758_ = lean_apply_2(v_inst_4752_, lean_box(0), v___x_4757_);
    return v___x_4758_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed(
    mut v___x_4759_: *mut LeanObject,
    mut v_knownSize_4760_: *mut LeanObject,
    mut v_inst_4761_: *mut LeanObject,
    mut v_____r_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_784__boxed_4764_: u8 = 0;
    let mut v_res_4765_: *mut LeanObject = core::ptr::null_mut();
    v___x_784__boxed_4764_ = (lean_unbox(v___x_4759_) as u8);
    v_res_4765_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0(
            v___x_784__boxed_4764_,
            v_knownSize_4760_,
            v_inst_4761_,
            v_____r_4762_,
            v___y_4763_,
        );
    lean_dec(v___y_4763_);
    return v_res_4765_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(
    mut v___f_4766_: *mut LeanObject,
    mut v___y_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4767_);
    v___x_4769_ = lean_apply_2(v___f_4766_, v_a_4768_, v___y_4767_);
    return v___x_4769_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed(
    mut v___f_4770_: *mut LeanObject,
    mut v___y_4771_: *mut LeanObject,
    mut v_a_4772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4773_: *mut LeanObject = core::ptr::null_mut();
    v_res_4773_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1(
            v___f_4770_,
            v___y_4771_,
            v_a_4772_,
        );
    lean_dec(v___y_4771_);
    return v_res_4773_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(
    mut v_pendingProducer_4774_: *mut LeanObject,
    mut v_toApplicative_4775_: *mut LeanObject,
    mut v___f_4776_: *mut LeanObject,
    mut v_closed_4777_: u8,
    mut v_inst_4778_: *mut LeanObject,
    mut v_toBind_4779_: *mut LeanObject,
    mut v_____r_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_pendingProducer_4774_) == 1 {
        let mut v_val_4782_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toFunctor_4783_: *mut LeanObject = core::ptr::null_mut();
        let mut v_done_4784_: *mut LeanObject = core::ptr::null_mut();
        let mut v_mapConst_4785_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
        v_val_4782_ = lean_ctor_get(v_pendingProducer_4774_, 0);
        lean_inc(v_val_4782_);
        lean_dec_ref_known(v_pendingProducer_4774_, 1);
        v_toFunctor_4783_ = lean_ctor_get(v_toApplicative_4775_, 0);
        lean_inc_ref(v_toFunctor_4783_);
        lean_dec_ref(v_toApplicative_4775_);
        v_done_4784_ = lean_ctor_get(v_val_4782_, 1);
        lean_inc(v_done_4784_);
        lean_dec(v_val_4782_);
        v_mapConst_4785_ = lean_ctor_get(v_toFunctor_4783_, 1);
        lean_inc(v_mapConst_4785_);
        lean_dec_ref(v_toFunctor_4783_);
        lean_inc(v___y_4781_);
        v___f_4786_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_4786_, 0, v___f_4776_);
        lean_closure_set(v___f_4786_, 1, v___y_4781_);
        v___x_4787_ = lean_box((v_closed_4777_) as usize);
        v___x_4788_ =
            lean_alloc_closure(l_IO_Promise_resolve___boxed as *mut core::ffi::c_void, 4, 3);
        lean_closure_set(v___x_4788_, 0, lean_box(0));
        lean_closure_set(v___x_4788_, 1, v___x_4787_);
        lean_closure_set(v___x_4788_, 2, v_done_4784_);
        v___x_4789_ = lean_apply_2(v_inst_4778_, lean_box(0), v___x_4788_);
        v___x_4790_ = lean_box(0);
        v___x_4791_ = lean_apply_4(
            v_mapConst_4785_,
            lean_box(0),
            lean_box(0),
            v___x_4790_,
            v___x_4789_,
        );
        v___x_4792_ = lean_apply_4(
            v_toBind_4779_,
            lean_box(0),
            lean_box(0),
            v___x_4791_,
            v___f_4786_,
        );
        return v___x_4792_;
    } else {
        let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_4779_);
        lean_dec(v_inst_4778_);
        lean_dec_ref(v_toApplicative_4775_);
        lean_dec(v_pendingProducer_4774_);
        v___x_4793_ = lean_box(0);
        lean_inc(v___y_4781_);
        v___x_4794_ = lean_apply_2(v___f_4776_, v___x_4793_, v___y_4781_);
        return v___x_4794_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed(
    mut v_pendingProducer_4795_: *mut LeanObject,
    mut v_toApplicative_4796_: *mut LeanObject,
    mut v___f_4797_: *mut LeanObject,
    mut v_closed_4798_: *mut LeanObject,
    mut v_inst_4799_: *mut LeanObject,
    mut v_toBind_4800_: *mut LeanObject,
    mut v_____r_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_4803_: u8 = 0;
    let mut v_res_4804_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_4803_ = (lean_unbox(v_closed_4798_) as u8);
    v_res_4804_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2(
            v_pendingProducer_4795_,
            v_toApplicative_4796_,
            v___f_4797_,
            v_closed_boxed_4803_,
            v_inst_4799_,
            v_toBind_4800_,
            v_____r_4801_,
            v___y_4802_,
        );
    lean_dec(v___y_4802_);
    return v_res_4804_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(
    mut v_interestWaiter_4805_: *mut LeanObject,
    mut v_toApplicative_4806_: *mut LeanObject,
    mut v___f_4807_: *mut LeanObject,
    mut v_closed_4808_: u8,
    mut v_inst_4809_: *mut LeanObject,
    mut v_toBind_4810_: *mut LeanObject,
    mut v_____r_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_interestWaiter_4805_) == 1 {
        let mut v_toFunctor_4813_: *mut LeanObject = core::ptr::null_mut();
        let mut v_val_4814_: *mut LeanObject = core::ptr::null_mut();
        let mut v_mapConst_4815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_4813_ = lean_ctor_get(v_toApplicative_4806_, 0);
        lean_inc_ref(v_toFunctor_4813_);
        lean_dec_ref(v_toApplicative_4806_);
        v_val_4814_ = lean_ctor_get(v_interestWaiter_4805_, 0);
        lean_inc(v_val_4814_);
        lean_dec_ref_known(v_interestWaiter_4805_, 1);
        v_mapConst_4815_ = lean_ctor_get(v_toFunctor_4813_, 1);
        lean_inc(v_mapConst_4815_);
        lean_dec_ref(v_toFunctor_4813_);
        lean_inc(v___y_4812_);
        v___f_4816_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_4816_, 0, v___f_4807_);
        lean_closure_set(v___f_4816_, 1, v___y_4812_);
        v___x_4817_ = lean_box((v_closed_4808_) as usize);
        v___x_4818_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___x_4818_, 0, v_val_4814_);
        lean_closure_set(v___x_4818_, 1, v___x_4817_);
        v___x_4819_ = lean_apply_2(v_inst_4809_, lean_box(0), v___x_4818_);
        v___x_4820_ = lean_box(0);
        v___x_4821_ = lean_apply_4(
            v_mapConst_4815_,
            lean_box(0),
            lean_box(0),
            v___x_4820_,
            v___x_4819_,
        );
        v___x_4822_ = lean_apply_4(
            v_toBind_4810_,
            lean_box(0),
            lean_box(0),
            v___x_4821_,
            v___f_4816_,
        );
        return v___x_4822_;
    } else {
        let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_4810_);
        lean_dec(v_inst_4809_);
        lean_dec_ref(v_toApplicative_4806_);
        lean_dec(v_interestWaiter_4805_);
        v___x_4823_ = lean_box(0);
        lean_inc(v___y_4812_);
        v___x_4824_ = lean_apply_2(v___f_4807_, v___x_4823_, v___y_4812_);
        return v___x_4824_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed(
    mut v_interestWaiter_4825_: *mut LeanObject,
    mut v_toApplicative_4826_: *mut LeanObject,
    mut v___f_4827_: *mut LeanObject,
    mut v_closed_4828_: *mut LeanObject,
    mut v_inst_4829_: *mut LeanObject,
    mut v_toBind_4830_: *mut LeanObject,
    mut v_____r_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_4833_: u8 = 0;
    let mut v_res_4834_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_4833_ = (lean_unbox(v_closed_4828_) as u8);
    v_res_4834_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(
            v_interestWaiter_4825_,
            v_toApplicative_4826_,
            v___f_4827_,
            v_closed_boxed_4833_,
            v_inst_4829_,
            v_toBind_4830_,
            v_____r_4831_,
            v___y_4832_,
        );
    lean_dec(v___y_4832_);
    return v_res_4834_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(
    mut v___f_4835_: *mut LeanObject,
    mut v_a_4836_: *mut LeanObject,
    mut v_a_4837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_4836_);
    v___x_4838_ = lean_apply_2(v___f_4835_, v_a_4837_, v_a_4836_);
    return v___x_4838_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed(
    mut v___f_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4842_: *mut LeanObject = core::ptr::null_mut();
    v_res_4842_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3(
            v___f_4839_,
            v_a_4840_,
            v_a_4841_,
        );
    lean_dec(v_a_4840_);
    return v_res_4842_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(
    mut v_inst_4843_: *mut LeanObject,
    mut v_toApplicative_4844_: *mut LeanObject,
    mut v_inst_4845_: *mut LeanObject,
    mut v_toBind_4846_: *mut LeanObject,
    mut v_a_4847_: *mut LeanObject,
    mut v_a_4848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_4849_: u8 = 0;
    v_closed_4849_ = lean_ctor_get_uint8(
        v_a_4848_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
    );
    if v_closed_4849_ == 0 {
        let mut v_pendingProducer_4850_: *mut LeanObject = core::ptr::null_mut();
        let mut v_pendingConsumer_4851_: *mut LeanObject = core::ptr::null_mut();
        let mut v_interestWaiter_4852_: *mut LeanObject = core::ptr::null_mut();
        let mut v_knownSize_4853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4854_: u8 = 0;
        let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4860_: *mut LeanObject = core::ptr::null_mut();
        v_pendingProducer_4850_ = lean_ctor_get(v_a_4848_, 0);
        lean_inc(v_pendingProducer_4850_);
        v_pendingConsumer_4851_ = lean_ctor_get(v_a_4848_, 1);
        lean_inc(v_pendingConsumer_4851_);
        v_interestWaiter_4852_ = lean_ctor_get(v_a_4848_, 2);
        lean_inc_n(v_interestWaiter_4852_, 2);
        v_knownSize_4853_ = lean_ctor_get(v_a_4848_, 3);
        lean_inc(v_knownSize_4853_);
        lean_dec_ref(v_a_4848_);
        v___x_4854_ = 1;
        v___x_4855_ = lean_box((v___x_4854_) as usize);
        v___f_4856_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
        lean_closure_set(v___f_4856_, 0, v___x_4855_);
        lean_closure_set(v___f_4856_, 1, v_knownSize_4853_);
        lean_closure_set(v___f_4856_, 2, v_inst_4843_);
        v___x_4857_ = lean_box((v_closed_4849_) as usize);
        lean_inc_n(v_toBind_4846_, 2);
        lean_inc_n(v_inst_4845_, 2);
        lean_inc_ref_n(v_toApplicative_4844_, 2);
        v___f_4858_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__2___boxed as *mut core::ffi::c_void, 8, 6);
        lean_closure_set(v___f_4858_, 0, v_pendingProducer_4850_);
        lean_closure_set(v___f_4858_, 1, v_toApplicative_4844_);
        lean_closure_set(v___f_4858_, 2, v___f_4856_);
        lean_closure_set(v___f_4858_, 3, v___x_4857_);
        lean_closure_set(v___f_4858_, 4, v_inst_4845_);
        lean_closure_set(v___f_4858_, 5, v_toBind_4846_);
        v___x_4859_ = lean_box((v_closed_4849_) as usize);
        lean_inc_ref(v___f_4858_);
        v___f_4860_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4___boxed as *mut core::ffi::c_void, 8, 6);
        lean_closure_set(v___f_4860_, 0, v_interestWaiter_4852_);
        lean_closure_set(v___f_4860_, 1, v_toApplicative_4844_);
        lean_closure_set(v___f_4860_, 2, v___f_4858_);
        lean_closure_set(v___f_4860_, 3, v___x_4859_);
        lean_closure_set(v___f_4860_, 4, v_inst_4845_);
        lean_closure_set(v___f_4860_, 5, v_toBind_4846_);
        if lean_obj_tag(v_pendingConsumer_4851_) == 1 {
            let mut v_toFunctor_4861_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_4862_: *mut LeanObject = core::ptr::null_mut();
            let mut v_mapConst_4863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___f_4858_);
            lean_dec(v_interestWaiter_4852_);
            v_toFunctor_4861_ = lean_ctor_get(v_toApplicative_4844_, 0);
            lean_inc_ref(v_toFunctor_4861_);
            lean_dec_ref(v_toApplicative_4844_);
            v_val_4862_ = lean_ctor_get(v_pendingConsumer_4851_, 0);
            lean_inc(v_val_4862_);
            lean_dec_ref_known(v_pendingConsumer_4851_, 1);
            v_mapConst_4863_ = lean_ctor_get(v_toFunctor_4861_, 1);
            lean_inc(v_mapConst_4863_);
            lean_dec_ref(v_toFunctor_4861_);
            lean_inc(v_a_4847_);
            v___f_4864_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 2);
            lean_closure_set(v___f_4864_, 0, v___f_4860_);
            lean_closure_set(v___f_4864_, 1, v_a_4847_);
            v___x_4865_ = lean_box(0);
            v___x_4866_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve___boxed as *mut core::ffi::c_void, 3, 2);
            lean_closure_set(v___x_4866_, 0, v_val_4862_);
            lean_closure_set(v___x_4866_, 1, v___x_4865_);
            v___x_4867_ = lean_apply_2(v_inst_4845_, lean_box(0), v___x_4866_);
            v___x_4868_ = lean_box(0);
            v___x_4869_ = lean_apply_4(
                v_mapConst_4863_,
                lean_box(0),
                lean_box(0),
                v___x_4868_,
                v___x_4867_,
            );
            v___x_4870_ = lean_apply_4(
                v_toBind_4846_,
                lean_box(0),
                lean_box(0),
                v___x_4869_,
                v___f_4864_,
            );
            return v___x_4870_;
        } else {
            let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___f_4860_);
            lean_dec(v_pendingConsumer_4851_);
            v___x_4871_ = lean_box(0);
            v___x_4872_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__4(v_interestWaiter_4852_, v_toApplicative_4844_, v___f_4858_, v_closed_4849_, v_inst_4845_, v_toBind_4846_, v___x_4871_, v_a_4847_);
            return v___x_4872_;
        }
    } else {
        let mut v_toPure_4873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_4848_);
        lean_dec(v_toBind_4846_);
        lean_dec(v_inst_4845_);
        lean_dec(v_inst_4843_);
        v_toPure_4873_ = lean_ctor_get(v_toApplicative_4844_, 1);
        lean_inc(v_toPure_4873_);
        lean_dec_ref(v_toApplicative_4844_);
        v___x_4874_ = lean_box(0);
        v___x_4875_ = lean_apply_2(v_toPure_4873_, lean_box(0), v___x_4874_);
        return v___x_4875_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed(
    mut v_inst_4876_: *mut LeanObject,
    mut v_toApplicative_4877_: *mut LeanObject,
    mut v_inst_4878_: *mut LeanObject,
    mut v_toBind_4879_: *mut LeanObject,
    mut v_a_4880_: *mut LeanObject,
    mut v_a_4881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4882_: *mut LeanObject = core::ptr::null_mut();
    v_res_4882_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5(
            v_inst_4876_,
            v_toApplicative_4877_,
            v_inst_4878_,
            v_toBind_4879_,
            v_a_4880_,
            v_a_4881_,
        );
    lean_dec(v_a_4880_);
    return v_res_4882_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(
    mut v_inst_4883_: *mut LeanObject,
    mut v_inst_4884_: *mut LeanObject,
    mut v_inst_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4887_ = lean_ctor_get(v_inst_4883_, 0);
    lean_inc_ref(v_toApplicative_4887_);
    v_toBind_4888_ = lean_ctor_get(v_inst_4883_, 1);
    lean_inc_n(v_toBind_4888_, 2);
    lean_dec_ref(v_inst_4883_);
    lean_inc_n(v_a_4886_, 2);
    lean_inc(v_inst_4884_);
    v___f_4889_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___lam__5___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_4889_, 0, v_inst_4884_);
    lean_closure_set(v___f_4889_, 1, v_toApplicative_4887_);
    lean_closure_set(v___f_4889_, 2, v_inst_4885_);
    lean_closure_set(v___f_4889_, 3, v_toBind_4888_);
    lean_closure_set(v___f_4889_, 4, v_a_4886_);
    v___x_4890_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4890_, 0, lean_box(0));
    lean_closure_set(v___x_4890_, 1, lean_box(0));
    lean_closure_set(v___x_4890_, 2, v_a_4886_);
    v___x_4891_ = lean_apply_2(v_inst_4884_, lean_box(0), v___x_4890_);
    v___x_4892_ = lean_apply_4(
        v_toBind_4888_,
        lean_box(0),
        lean_box(0),
        v___x_4891_,
        v___f_4889_,
    );
    return v___x_4892_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg___boxed(
    mut v_inst_4893_: *mut LeanObject,
    mut v_inst_4894_: *mut LeanObject,
    mut v_inst_4895_: *mut LeanObject,
    mut v_a_4896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4897_: *mut LeanObject = core::ptr::null_mut();
    v_res_4897_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(
        v_inst_4893_,
        v_inst_4894_,
        v_inst_4895_,
        v_a_4896_,
    );
    lean_dec(v_a_4896_);
    return v_res_4897_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(
    mut v_m_4898_: *mut LeanObject,
    mut v_inst_4899_: *mut LeanObject,
    mut v_inst_4900_: *mut LeanObject,
    mut v_inst_4901_: *mut LeanObject,
    mut v_a_4902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    v___x_4903_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___redArg(
        v_inst_4899_,
        v_inst_4900_,
        v_inst_4901_,
        v_a_4902_,
    );
    return v___x_4903_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___boxed(
    mut v_m_4904_: *mut LeanObject,
    mut v_inst_4905_: *mut LeanObject,
    mut v_inst_4906_: *mut LeanObject,
    mut v_inst_4907_: *mut LeanObject,
    mut v_a_4908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4909_: *mut LeanObject = core::ptr::null_mut();
    v_res_4909_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27(
        v_m_4904_,
        v_inst_4905_,
        v_inst_4906_,
        v_inst_4907_,
        v_a_4908_,
    );
    lean_dec(v_a_4908_);
    return v_res_4909_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(
    mut v_chunk_4910_: *mut LeanObject,
    mut v_x_4911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4921_: u8 = 0;
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut v_unused_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4911_) == 0 {
                    lean_dec_ref(v_chunk_4910_);
                    v_a_4913_ = lean_ctor_get(v_x_4911_, 0);
                    v_isSharedCheck_4921_ = (!lean_is_exclusive(v_x_4911_)) as u8;
                    if v_isSharedCheck_4921_ == 0 {
                        v___x_4915_ = v_x_4911_;
                        v_isShared_4916_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4913_);
                        lean_dec(v_x_4911_);
                        v___x_4915_ = lean_box(0);
                        v_isShared_4916_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_4930_ = (!lean_is_exclusive(v_x_4911_)) as u8;
                    if v_isSharedCheck_4930_ == 0 {
                        v_unused_4931_ = lean_ctor_get(v_x_4911_, 0);
                        lean_dec(v_unused_4931_);
                        v___x_4923_ = v_x_4911_;
                        v_isShared_4924_ = v_isSharedCheck_4930_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_4911_);
                        v___x_4923_ = lean_box(0);
                        v_isShared_4924_ = v_isSharedCheck_4930_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4916_ == 0 {
                    v___x_4918_ = v___x_4915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4913_);
                    v___x_4918_ = v_reuseFailAlloc_4920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4919_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4919_, 0, v___x_4918_);
                return v___x_4919_;
            }
            3 => {
                v___x_4925_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4925_, 0, v_chunk_4910_);
                if v_isShared_4924_ == 0 {
                    lean_ctor_set(v___x_4923_, 0, v___x_4925_);
                    v___x_4927_ = v___x_4923_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4925_);
                    v___x_4927_ = v_reuseFailAlloc_4929_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4928_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4928_, 0, v___x_4927_);
                return v___x_4928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed(
    mut v_chunk_4932_: *mut LeanObject,
    mut v_x_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4935_: *mut LeanObject = core::ptr::null_mut();
    v_res_4935_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0(v_chunk_4932_, v_x_4933_);
    return v_res_4935_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(
    mut v_done_4940_: *mut LeanObject,
    mut v___f_4941_: *mut LeanObject,
    mut v_x_4942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: u8 = 0;
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4942_) == 0 {
                    lean_dec_ref(v___f_4941_);
                    v_a_4944_ = lean_ctor_get(v_x_4942_, 0);
                    v_isSharedCheck_4952_ = (!lean_is_exclusive(v_x_4942_)) as u8;
                    if v_isSharedCheck_4952_ == 0 {
                        v___x_4946_ = v_x_4942_;
                        v_isShared_4947_ = v_isSharedCheck_4952_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4944_);
                        lean_dec(v_x_4942_);
                        v___x_4946_ = lean_box(0);
                        v_isShared_4947_ = v_isSharedCheck_4952_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_4942_, 1);
                    v___x_4953_ = 1;
                    v___x_4954_ = lean_box((v___x_4953_) as usize);
                    v___x_4955_ = lean_io_promise_resolve(v___x_4954_, v_done_4940_);
                    v___x_4956_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                    v___x_4957_ = lean_unsigned_to_nat(0);
                    v___x_4958_ = 0;
                    v___x_4959_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_4957_,
                            v___x_4958_,
                            v___x_4956_,
                            v___f_4941_,
                        );
                    return v___x_4959_;
                }
            }
            1 => {
                if v_isShared_4947_ == 0 {
                    v___x_4949_ = v___x_4946_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4944_);
                    v___x_4949_ = v_reuseFailAlloc_4951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4950_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4950_, 0, v___x_4949_);
                return v___x_4950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed(
    mut v_done_4960_: *mut LeanObject,
    mut v___f_4961_: *mut LeanObject,
    mut v_x_4962_: *mut LeanObject,
    mut v___y_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4964_: *mut LeanObject = core::ptr::null_mut();
    v_res_4964_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1(v_done_4960_, v___f_4961_, v_x_4962_);
    lean_dec(v_done_4960_);
    return v_res_4964_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(
    mut v_a_4969_: *mut LeanObject,
    mut v_x_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_a_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v_pendingProducer_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4989_: u8 = 0;
    let mut v_pendingConsumer_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_4992_: u8 = 0;
    let mut v_knownSize_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4997_: u8 = 0;
    let mut v_chunk_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5019_: u8 = 0;
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4970_) == 0 {
                    v_a_4972_ = lean_ctor_get(v_x_4970_, 0);
                    v_isSharedCheck_4980_ = (!lean_is_exclusive(v_x_4970_)) as u8;
                    if v_isSharedCheck_4980_ == 0 {
                        v___x_4974_ = v_x_4970_;
                        v_isShared_4975_ = v_isSharedCheck_4980_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4972_);
                        lean_dec(v_x_4970_);
                        v___x_4974_ = lean_box(0);
                        v_isShared_4975_ = v_isSharedCheck_4980_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4981_ = lean_ctor_get(v_x_4970_, 0);
                    v_isSharedCheck_5021_ = (!lean_is_exclusive(v_x_4970_)) as u8;
                    if v_isSharedCheck_5021_ == 0 {
                        v___x_4983_ = v_x_4970_;
                        v_isShared_4984_ = v_isSharedCheck_5021_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4981_);
                        lean_dec(v_x_4970_);
                        v___x_4983_ = lean_box(0);
                        v_isShared_4984_ = v_isSharedCheck_5021_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4975_ == 0 {
                    v___x_4977_ = v___x_4974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4972_);
                    v___x_4977_ = v_reuseFailAlloc_4979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4978_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4978_, 0, v___x_4977_);
                return v___x_4978_;
            }
            3 => {
                v_pendingProducer_4985_ = lean_ctor_get(v_a_4981_, 0);
                lean_inc(v_pendingProducer_4985_);
                if lean_obj_tag(v_pendingProducer_4985_) == 1 {
                    v_val_4986_ = lean_ctor_get(v_pendingProducer_4985_, 0);
                    v_isSharedCheck_5019_ = (!lean_is_exclusive(v_pendingProducer_4985_)) as u8;
                    if v_isSharedCheck_5019_ == 0 {
                        v___x_4988_ = v_pendingProducer_4985_;
                        v_isShared_4989_ = v_isSharedCheck_5019_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_4986_);
                        lean_dec(v_pendingProducer_4985_);
                        v___x_4988_ = lean_box(0);
                        v_isShared_4989_ = v_isSharedCheck_5019_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_pendingProducer_4985_);
                    lean_del_object(v___x_4983_);
                    lean_dec(v_a_4981_);
                    v___x_5020_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1;
                    return v___x_5020_;
                }
            }
            4 => {
                v_pendingConsumer_4990_ = lean_ctor_get(v_a_4981_, 1);
                v_interestWaiter_4991_ = lean_ctor_get(v_a_4981_, 2);
                v_closed_4992_ = lean_ctor_get_uint8(
                    v_a_4981_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_knownSize_4993_ = lean_ctor_get(v_a_4981_, 3);
                v_pendingIncompleteChunk_4994_ = lean_ctor_get(v_a_4981_, 4);
                v_isSharedCheck_5017_ = (!lean_is_exclusive(v_a_4981_)) as u8;
                if v_isSharedCheck_5017_ == 0 {
                    v_unused_5018_ = lean_ctor_get(v_a_4981_, 0);
                    lean_dec(v_unused_5018_);
                    v___x_4996_ = v_a_4981_;
                    v_isShared_4997_ = v_isSharedCheck_5017_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_pendingIncompleteChunk_4994_);
                    lean_inc(v_knownSize_4993_);
                    lean_inc(v_interestWaiter_4991_);
                    lean_inc(v_pendingConsumer_4990_);
                    lean_dec(v_a_4981_);
                    v___x_4996_ = lean_box(0);
                    v_isShared_4997_ = v_isSharedCheck_5017_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_chunk_4998_ = lean_ctor_get(v_val_4986_, 0);
                lean_inc_ref(v_chunk_4998_);
                v_done_4999_ = lean_ctor_get(v_val_4986_, 1);
                lean_inc(v_done_4999_);
                lean_dec(v_val_4986_);
                v___x_5000_ = lean_box(0);
                v___x_5001_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_4993_, v_chunk_4998_);
                if v_isShared_4997_ == 0 {
                    lean_ctor_set(v___x_4996_, 3, v___x_5001_);
                    lean_ctor_set(v___x_4996_, 0, v___x_5000_);
                    v___x_5003_ = v___x_4996_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5000_);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_pendingConsumer_4990_);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 2, v_interestWaiter_4991_);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 3, v___x_5001_);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 4, v_pendingIncompleteChunk_4994_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5016_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_4992_,
                    );
                    v___x_5003_ = v_reuseFailAlloc_5016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5004_ = lean_st_ref_set(v_a_4969_, v___x_5003_);
                v___f_5005_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_5005_, 0, v_chunk_4998_);
                v___f_5006_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_5006_, 0, v_done_4999_);
                lean_closure_set(v___f_5006_, 1, v___f_5005_);
                if v_isShared_4984_ == 0 {
                    lean_ctor_set(v___x_4983_, 0, v___x_5004_);
                    v___x_5008_ = v___x_4983_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5004_);
                    v___x_5008_ = v_reuseFailAlloc_5015_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4989_ == 0 {
                    lean_ctor_set_tag(v___x_4988_, 0);
                    lean_ctor_set(v___x_4988_, 0, v___x_5008_);
                    v___x_5010_ = v___x_4988_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5008_);
                    v___x_5010_ = v_reuseFailAlloc_5014_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5011_ = lean_unsigned_to_nat(0);
                v___x_5012_ = 0;
                v___x_5013_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_5011_,
                    v___x_5012_,
                    v___x_5010_,
                    v___f_5006_,
                );
                return v___x_5013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed(
    mut v_a_5022_: *mut LeanObject,
    mut v_x_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5025_: *mut LeanObject = core::ptr::null_mut();
    v_res_5025_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2(v_a_5022_, v_x_5023_);
    lean_dec(v_a_5022_);
    return v_res_5025_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(
    mut v_a_5026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    v___x_5028_ = lean_st_ref_get(v_a_5026_);
    lean_inc(v_a_5026_);
    v___f_5029_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5029_, 0, v_a_5026_);
    v___x_5030_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5030_, 0, v___x_5028_);
    v___x_5031_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5031_, 0, v___x_5030_);
    v___x_5032_ = lean_unsigned_to_nat(0);
    v___x_5033_ = 0;
    v___x_5034_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5032_,
        v___x_5033_,
        v___x_5031_,
        v___f_5029_,
    );
    return v___x_5034_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___boxed(
    mut v_a_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5037_: *mut LeanObject = core::ptr::null_mut();
    v_res_5037_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v_a_5035_);
    lean_dec(v_a_5035_);
    return v_res_5037_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(
    mut v_pendingProducer_5038_: *mut LeanObject,
    mut v_pendingConsumer_5039_: *mut LeanObject,
    mut v_closed_5040_: u8,
    mut v_knownSize_5041_: *mut LeanObject,
    mut v_pendingIncompleteChunk_5042_: *mut LeanObject,
    mut v_interestWaiter_5043_: *mut LeanObject,
    mut v___y_5044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    v___x_5046_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_5046_, 0, v_pendingProducer_5038_);
    lean_ctor_set(v___x_5046_, 1, v_pendingConsumer_5039_);
    lean_ctor_set(v___x_5046_, 2, v_interestWaiter_5043_);
    lean_ctor_set(v___x_5046_, 3, v_knownSize_5041_);
    lean_ctor_set(v___x_5046_, 4, v_pendingIncompleteChunk_5042_);
    lean_ctor_set_uint8(
        v___x_5046_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v_closed_5040_,
    );
    v___x_5047_ = lean_st_ref_set(v___y_5044_, v___x_5046_);
    v___x_5048_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5048_, 0, v___x_5047_);
    v___x_5049_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5049_, 0, v___x_5048_);
    return v___x_5049_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed(
    mut v_pendingProducer_5050_: *mut LeanObject,
    mut v_pendingConsumer_5051_: *mut LeanObject,
    mut v_closed_5052_: *mut LeanObject,
    mut v_knownSize_5053_: *mut LeanObject,
    mut v_pendingIncompleteChunk_5054_: *mut LeanObject,
    mut v_interestWaiter_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_5058_: u8 = 0;
    let mut v_res_5059_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_5058_ = (lean_unbox(v_closed_5052_) as u8);
    v_res_5059_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0(v_pendingProducer_5050_, v_pendingConsumer_5051_, v_closed_boxed_5058_, v_knownSize_5053_, v_pendingIncompleteChunk_5054_, v_interestWaiter_5055_, v___y_5056_);
    lean_dec(v___y_5056_);
    return v_res_5059_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(
    mut v___f_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v_x_5062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5067_: u8 = 0;
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5072_: u8 = 0;
    let mut v_a_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5062_) == 0 {
                    lean_dec_ref(v___f_5060_);
                    v_a_5064_ = lean_ctor_get(v_x_5062_, 0);
                    v_isSharedCheck_5072_ = (!lean_is_exclusive(v_x_5062_)) as u8;
                    if v_isSharedCheck_5072_ == 0 {
                        v___x_5066_ = v_x_5062_;
                        v_isShared_5067_ = v_isSharedCheck_5072_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5064_);
                        lean_dec(v_x_5062_);
                        v___x_5066_ = lean_box(0);
                        v_isShared_5067_ = v_isSharedCheck_5072_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5073_ = lean_ctor_get(v_x_5062_, 0);
                    lean_inc(v_a_5073_);
                    lean_dec_ref_known(v_x_5062_, 1);
                    lean_inc(v___y_5061_);
                    v___x_5074_ = lean_apply_3(v___f_5060_, v_a_5073_, v___y_5061_, lean_box(0));
                    return v___x_5074_;
                }
            }
            1 => {
                if v_isShared_5067_ == 0 {
                    v___x_5069_ = v___x_5066_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5064_);
                    v___x_5069_ = v_reuseFailAlloc_5071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5070_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5070_, 0, v___x_5069_);
                return v___x_5070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed(
    mut v___f_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v_x_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5079_: *mut LeanObject = core::ptr::null_mut();
    v_res_5079_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1(v___f_5075_, v___y_5076_, v_x_5077_);
    lean_dec(v___y_5076_);
    return v_res_5079_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(
    mut v_interestWaiter_5084_: *mut LeanObject,
    mut v___f_5085_: *mut LeanObject,
    mut v___f_5086_: *mut LeanObject,
    mut v_x_5087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5097_: u8 = 0;
    let mut v_a_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5101_: u8 = 0;
    let mut v___x_5102_: u8 = 0;
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: u8 = 0;
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5087_) == 0 {
                    lean_dec_ref(v___f_5086_);
                    lean_dec_ref(v___f_5085_);
                    lean_dec(v_interestWaiter_5084_);
                    v_a_5089_ = lean_ctor_get(v_x_5087_, 0);
                    v_isSharedCheck_5097_ = (!lean_is_exclusive(v_x_5087_)) as u8;
                    if v_isSharedCheck_5097_ == 0 {
                        v___x_5091_ = v_x_5087_;
                        v_isShared_5092_ = v_isSharedCheck_5097_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5089_);
                        lean_dec(v_x_5087_);
                        v___x_5091_ = lean_box(0);
                        v_isShared_5092_ = v_isSharedCheck_5097_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5098_ = lean_ctor_get(v_x_5087_, 0);
                    v_isSharedCheck_5114_ = (!lean_is_exclusive(v_x_5087_)) as u8;
                    if v_isSharedCheck_5114_ == 0 {
                        v___x_5100_ = v_x_5087_;
                        v_isShared_5101_ = v_isSharedCheck_5114_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5098_);
                        lean_dec(v_x_5087_);
                        v___x_5100_ = lean_box(0);
                        v_isShared_5101_ = v_isSharedCheck_5114_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5092_ == 0 {
                    v___x_5094_ = v___x_5091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5089_);
                    v___x_5094_ = v_reuseFailAlloc_5096_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5095_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5095_, 0, v___x_5094_);
                return v___x_5095_;
            }
            3 => {
                v___x_5102_ = (lean_unbox(v_a_5098_) as u8);
                if v___x_5102_ == 0 {
                    lean_dec_ref(v___f_5086_);
                    if v_isShared_5101_ == 0 {
                        lean_ctor_set(v___x_5100_, 0, v_interestWaiter_5084_);
                        v___x_5104_ = v___x_5100_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_interestWaiter_5084_);
                        v___x_5104_ = v_reuseFailAlloc_5109_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5100_);
                    lean_dec(v_a_5098_);
                    lean_dec_ref(v___f_5085_);
                    lean_dec(v_interestWaiter_5084_);
                    v___x_5110_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___closed__1;
                    v___x_5111_ = lean_unsigned_to_nat(0);
                    v___x_5112_ = 0;
                    v___x_5113_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_5111_,
                            v___x_5112_,
                            v___x_5110_,
                            v___f_5086_,
                        );
                    return v___x_5113_;
                }
            }
            4 => {
                v___x_5105_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5105_, 0, v___x_5104_);
                v___x_5106_ = lean_unsigned_to_nat(0);
                v___x_5107_ = (lean_unbox(v_a_5098_) as u8);
                lean_dec(v_a_5098_);
                v___x_5108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_5106_,
                    v___x_5107_,
                    v___x_5105_,
                    v___f_5085_,
                );
                return v___x_5108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed(
    mut v_interestWaiter_5115_: *mut LeanObject,
    mut v___f_5116_: *mut LeanObject,
    mut v___f_5117_: *mut LeanObject,
    mut v_x_5118_: *mut LeanObject,
    mut v___y_5119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5120_: *mut LeanObject = core::ptr::null_mut();
    v_res_5120_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4(v_interestWaiter_5115_, v___f_5116_, v___f_5117_, v_x_5118_);
    return v_res_5120_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(
    mut v_pendingProducer_5121_: *mut LeanObject,
    mut v_closed_5122_: u8,
    mut v_knownSize_5123_: *mut LeanObject,
    mut v_pendingIncompleteChunk_5124_: *mut LeanObject,
    mut v_interestWaiter_5125_: *mut LeanObject,
    mut v_pendingConsumer_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut LeanObject = core::ptr::null_mut();
    v___x_5129_ = lean_box((v_closed_5122_) as usize);
    v___f_5130_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__0___boxed as *mut core::ffi::c_void, 8, 5);
    lean_closure_set(v___f_5130_, 0, v_pendingProducer_5121_);
    lean_closure_set(v___f_5130_, 1, v_pendingConsumer_5126_);
    lean_closure_set(v___f_5130_, 2, v___x_5129_);
    lean_closure_set(v___f_5130_, 3, v_knownSize_5123_);
    lean_closure_set(v___f_5130_, 4, v_pendingIncompleteChunk_5124_);
    if lean_obj_tag(v_interestWaiter_5125_) == 0 {
        let mut v___f_5131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5135_: u8 = 0;
        let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_5127_);
        v___f_5131_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
        lean_closure_set(v___f_5131_, 0, v___f_5130_);
        lean_closure_set(v___f_5131_, 1, v___y_5127_);
        v___x_5132_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5132_, 0, v_interestWaiter_5125_);
        v___x_5133_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5133_, 0, v___x_5132_);
        v___x_5134_ = lean_unsigned_to_nat(0);
        v___x_5135_ = 0;
        v___x_5136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_5134_,
            v___x_5135_,
            v___x_5133_,
            v___f_5131_,
        );
        return v___x_5136_;
    } else {
        let mut v_val_5137_: *mut LeanObject = core::ptr::null_mut();
        let mut v_finished_5138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5145_: u8 = 0;
        let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
        v_val_5137_ = lean_ctor_get(v_interestWaiter_5125_, 0);
        v_finished_5138_ = lean_ctor_get(v_val_5137_, 0);
        v___x_5139_ = lean_st_ref_get(v_finished_5138_);
        lean_inc(v___y_5127_);
        v___f_5140_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
        lean_closure_set(v___f_5140_, 0, v___f_5130_);
        lean_closure_set(v___f_5140_, 1, v___y_5127_);
        lean_inc_ref(v___f_5140_);
        v___f_5141_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__4___boxed as *mut core::ffi::c_void, 5, 3);
        lean_closure_set(v___f_5141_, 0, v_interestWaiter_5125_);
        lean_closure_set(v___f_5141_, 1, v___f_5140_);
        lean_closure_set(v___f_5141_, 2, v___f_5140_);
        v___x_5142_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5142_, 0, v___x_5139_);
        v___x_5143_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5143_, 0, v___x_5142_);
        v___x_5144_ = lean_unsigned_to_nat(0);
        v___x_5145_ = 0;
        v___x_5146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_5144_,
            v___x_5145_,
            v___x_5143_,
            v___f_5141_,
        );
        return v___x_5146_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed(
    mut v_pendingProducer_5147_: *mut LeanObject,
    mut v_closed_5148_: *mut LeanObject,
    mut v_knownSize_5149_: *mut LeanObject,
    mut v_pendingIncompleteChunk_5150_: *mut LeanObject,
    mut v_interestWaiter_5151_: *mut LeanObject,
    mut v_pendingConsumer_5152_: *mut LeanObject,
    mut v___y_5153_: *mut LeanObject,
    mut v___y_5154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_5155_: u8 = 0;
    let mut v_res_5156_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_5155_ = (lean_unbox(v_closed_5148_) as u8);
    v_res_5156_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2(v_pendingProducer_5147_, v_closed_boxed_5155_, v_knownSize_5149_, v_pendingIncompleteChunk_5150_, v_interestWaiter_5151_, v_pendingConsumer_5152_, v___y_5153_);
    lean_dec(v___y_5153_);
    return v_res_5156_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(
    mut v___f_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v_x_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5169_: u8 = 0;
    let mut v_a_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5159_) == 0 {
                    lean_dec_ref(v___f_5157_);
                    v_a_5161_ = lean_ctor_get(v_x_5159_, 0);
                    v_isSharedCheck_5169_ = (!lean_is_exclusive(v_x_5159_)) as u8;
                    if v_isSharedCheck_5169_ == 0 {
                        v___x_5163_ = v_x_5159_;
                        v_isShared_5164_ = v_isSharedCheck_5169_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5161_);
                        lean_dec(v_x_5159_);
                        v___x_5163_ = lean_box(0);
                        v_isShared_5164_ = v_isSharedCheck_5169_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5170_ = lean_ctor_get(v_x_5159_, 0);
                    lean_inc(v_a_5170_);
                    lean_dec_ref_known(v_x_5159_, 1);
                    lean_inc(v___y_5158_);
                    v___x_5171_ = lean_apply_3(v___f_5157_, v_a_5170_, v___y_5158_, lean_box(0));
                    return v___x_5171_;
                }
            }
            1 => {
                if v_isShared_5164_ == 0 {
                    v___x_5166_ = v___x_5163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5161_);
                    v___x_5166_ = v_reuseFailAlloc_5168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5167_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5167_, 0, v___x_5166_);
                return v___x_5167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed(
    mut v___f_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v_x_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5176_: *mut LeanObject = core::ptr::null_mut();
    v_res_5176_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3(v___f_5172_, v___y_5173_, v_x_5174_);
    lean_dec(v___y_5173_);
    return v_res_5176_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(
    mut v___f_5177_: *mut LeanObject,
    mut v_a_5178_: *mut LeanObject,
    mut v_x_5179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5189_: u8 = 0;
    let mut v_a_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5179_) == 0 {
                    lean_dec_ref(v___f_5177_);
                    v_a_5181_ = lean_ctor_get(v_x_5179_, 0);
                    v_isSharedCheck_5189_ = (!lean_is_exclusive(v_x_5179_)) as u8;
                    if v_isSharedCheck_5189_ == 0 {
                        v___x_5183_ = v_x_5179_;
                        v_isShared_5184_ = v_isSharedCheck_5189_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5181_);
                        lean_dec(v_x_5179_);
                        v___x_5183_ = lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5189_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5190_ = lean_ctor_get(v_x_5179_, 0);
                    lean_inc(v_a_5190_);
                    lean_dec_ref_known(v_x_5179_, 1);
                    lean_inc(v_a_5178_);
                    v___x_5191_ = lean_apply_3(v___f_5177_, v_a_5190_, v_a_5178_, lean_box(0));
                    return v___x_5191_;
                }
            }
            1 => {
                if v_isShared_5184_ == 0 {
                    v___x_5186_ = v___x_5183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5187_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5187_, 0, v___x_5186_);
                return v___x_5187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed(
    mut v___f_5192_: *mut LeanObject,
    mut v_a_5193_: *mut LeanObject,
    mut v_x_5194_: *mut LeanObject,
    mut v___y_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5196_: *mut LeanObject = core::ptr::null_mut();
    v_res_5196_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5(v___f_5192_, v_a_5193_, v_x_5194_);
    lean_dec(v_a_5193_);
    return v_res_5196_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(
    mut v_pendingConsumer_5201_: *mut LeanObject,
    mut v___f_5202_: *mut LeanObject,
    mut v___f_5203_: *mut LeanObject,
    mut v_x_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_a_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5218_: u8 = 0;
    let mut v___x_5219_: u8 = 0;
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: u8 = 0;
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: u8 = 0;
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5204_) == 0 {
                    lean_dec_ref(v___f_5203_);
                    lean_dec_ref(v___f_5202_);
                    lean_dec(v_pendingConsumer_5201_);
                    v_a_5206_ = lean_ctor_get(v_x_5204_, 0);
                    v_isSharedCheck_5214_ = (!lean_is_exclusive(v_x_5204_)) as u8;
                    if v_isSharedCheck_5214_ == 0 {
                        v___x_5208_ = v_x_5204_;
                        v_isShared_5209_ = v_isSharedCheck_5214_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5206_);
                        lean_dec(v_x_5204_);
                        v___x_5208_ = lean_box(0);
                        v_isShared_5209_ = v_isSharedCheck_5214_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5215_ = lean_ctor_get(v_x_5204_, 0);
                    v_isSharedCheck_5231_ = (!lean_is_exclusive(v_x_5204_)) as u8;
                    if v_isSharedCheck_5231_ == 0 {
                        v___x_5217_ = v_x_5204_;
                        v_isShared_5218_ = v_isSharedCheck_5231_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5215_);
                        lean_dec(v_x_5204_);
                        v___x_5217_ = lean_box(0);
                        v_isShared_5218_ = v_isSharedCheck_5231_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5209_ == 0 {
                    v___x_5211_ = v___x_5208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5206_);
                    v___x_5211_ = v_reuseFailAlloc_5213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5212_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5212_, 0, v___x_5211_);
                return v___x_5212_;
            }
            3 => {
                v___x_5219_ = (lean_unbox(v_a_5215_) as u8);
                if v___x_5219_ == 0 {
                    lean_dec_ref(v___f_5203_);
                    if v_isShared_5218_ == 0 {
                        lean_ctor_set(v___x_5217_, 0, v_pendingConsumer_5201_);
                        v___x_5221_ = v___x_5217_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_pendingConsumer_5201_);
                        v___x_5221_ = v_reuseFailAlloc_5226_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5217_);
                    lean_dec(v_a_5215_);
                    lean_dec_ref(v___f_5202_);
                    lean_dec(v_pendingConsumer_5201_);
                    v___x_5227_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___closed__1;
                    v___x_5228_ = lean_unsigned_to_nat(0);
                    v___x_5229_ = 0;
                    v___x_5230_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_5228_,
                            v___x_5229_,
                            v___x_5227_,
                            v___f_5203_,
                        );
                    return v___x_5230_;
                }
            }
            4 => {
                v___x_5222_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5222_, 0, v___x_5221_);
                v___x_5223_ = lean_unsigned_to_nat(0);
                v___x_5224_ = (lean_unbox(v_a_5215_) as u8);
                lean_dec(v_a_5215_);
                v___x_5225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_5223_,
                    v___x_5224_,
                    v___x_5222_,
                    v___f_5202_,
                );
                return v___x_5225_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed(
    mut v_pendingConsumer_5232_: *mut LeanObject,
    mut v___f_5233_: *mut LeanObject,
    mut v___f_5234_: *mut LeanObject,
    mut v_x_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5237_: *mut LeanObject = core::ptr::null_mut();
    v_res_5237_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7(v_pendingConsumer_5232_, v___f_5233_, v___f_5234_, v_x_5235_);
    return v_res_5237_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(
    mut v_a_5238_: *mut LeanObject,
    mut v_x_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5244_: u8 = 0;
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5249_: u8 = 0;
    let mut v_a_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5253_: u8 = 0;
    let mut v_pendingProducer_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5257_: u8 = 0;
    let mut v_knownSize_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5276_: u8 = 0;
    let mut v_finished_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: u8 = 0;
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v_isSharedCheck_5289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5239_) == 0 {
                    v_a_5241_ = lean_ctor_get(v_x_5239_, 0);
                    v_isSharedCheck_5249_ = (!lean_is_exclusive(v_x_5239_)) as u8;
                    if v_isSharedCheck_5249_ == 0 {
                        v___x_5243_ = v_x_5239_;
                        v_isShared_5244_ = v_isSharedCheck_5249_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5241_);
                        lean_dec(v_x_5239_);
                        v___x_5243_ = lean_box(0);
                        v_isShared_5244_ = v_isSharedCheck_5249_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5250_ = lean_ctor_get(v_x_5239_, 0);
                    v_isSharedCheck_5289_ = (!lean_is_exclusive(v_x_5239_)) as u8;
                    if v_isSharedCheck_5289_ == 0 {
                        v___x_5252_ = v_x_5239_;
                        v_isShared_5253_ = v_isSharedCheck_5289_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5250_);
                        lean_dec(v_x_5239_);
                        v___x_5252_ = lean_box(0);
                        v_isShared_5253_ = v_isSharedCheck_5289_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5244_ == 0 {
                    v___x_5246_ = v___x_5243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5241_);
                    v___x_5246_ = v_reuseFailAlloc_5248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5247_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5247_, 0, v___x_5246_);
                return v___x_5247_;
            }
            3 => {
                v_pendingProducer_5254_ = lean_ctor_get(v_a_5250_, 0);
                lean_inc(v_pendingProducer_5254_);
                v_pendingConsumer_5255_ = lean_ctor_get(v_a_5250_, 1);
                lean_inc(v_pendingConsumer_5255_);
                v_interestWaiter_5256_ = lean_ctor_get(v_a_5250_, 2);
                lean_inc(v_interestWaiter_5256_);
                v_closed_5257_ = lean_ctor_get_uint8(
                    v_a_5250_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_knownSize_5258_ = lean_ctor_get(v_a_5250_, 3);
                lean_inc(v_knownSize_5258_);
                v_pendingIncompleteChunk_5259_ = lean_ctor_get(v_a_5250_, 4);
                lean_inc(v_pendingIncompleteChunk_5259_);
                lean_dec(v_a_5250_);
                v___x_5260_ = lean_box((v_closed_5257_) as usize);
                v___f_5261_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__2___boxed as *mut core::ffi::c_void, 8, 5);
                lean_closure_set(v___f_5261_, 0, v_pendingProducer_5254_);
                lean_closure_set(v___f_5261_, 1, v___x_5260_);
                lean_closure_set(v___f_5261_, 2, v_knownSize_5258_);
                lean_closure_set(v___f_5261_, 3, v_pendingIncompleteChunk_5259_);
                lean_closure_set(v___f_5261_, 4, v_interestWaiter_5256_);
                if lean_obj_tag(v_pendingConsumer_5255_) == 1 {
                    v_val_5272_ = lean_ctor_get(v_pendingConsumer_5255_, 0);
                    lean_inc(v_val_5272_);
                    if lean_obj_tag(v_val_5272_) == 1 {
                        lean_del_object(v___x_5252_);
                        v_finished_5273_ = lean_ctor_get(v_val_5272_, 0);
                        v_isSharedCheck_5288_ = (!lean_is_exclusive(v_val_5272_)) as u8;
                        if v_isSharedCheck_5288_ == 0 {
                            v___x_5275_ = v_val_5272_;
                            v_isShared_5276_ = v_isSharedCheck_5288_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_finished_5273_);
                            lean_dec(v_val_5272_);
                            v___x_5275_ = lean_box(0);
                            v_isShared_5276_ = v_isSharedCheck_5288_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_5272_);
                        v___y_5263_ = v_a_5238_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_5263_ = v_a_5238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v___y_5263_);
                v___f_5264_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_5264_, 0, v___f_5261_);
                lean_closure_set(v___f_5264_, 1, v___y_5263_);
                if v_isShared_5253_ == 0 {
                    lean_ctor_set(v___x_5252_, 0, v_pendingConsumer_5255_);
                    v___x_5266_ = v___x_5252_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_pendingConsumer_5255_);
                    v___x_5266_ = v_reuseFailAlloc_5271_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5267_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5267_, 0, v___x_5266_);
                v___x_5268_ = lean_unsigned_to_nat(0);
                v___x_5269_ = 0;
                v___x_5270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_5268_,
                    v___x_5269_,
                    v___x_5267_,
                    v___f_5264_,
                );
                return v___x_5270_;
            }
            6 => {
                v_finished_5277_ = lean_ctor_get(v_finished_5273_, 0);
                lean_inc(v_finished_5277_);
                lean_dec_ref(v_finished_5273_);
                v___x_5278_ = lean_st_ref_get(v_finished_5277_);
                lean_dec(v_finished_5277_);
                lean_inc(v_a_5238_);
                v___f_5279_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__5___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_5279_, 0, v___f_5261_);
                lean_closure_set(v___f_5279_, 1, v_a_5238_);
                lean_inc_ref(v___f_5279_);
                v___f_5280_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__7___boxed as *mut core::ffi::c_void, 5, 3);
                lean_closure_set(v___f_5280_, 0, v_pendingConsumer_5255_);
                lean_closure_set(v___f_5280_, 1, v___f_5279_);
                lean_closure_set(v___f_5280_, 2, v___f_5279_);
                if v_isShared_5276_ == 0 {
                    lean_ctor_set(v___x_5275_, 0, v___x_5278_);
                    v___x_5282_ = v___x_5275_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5278_);
                    v___x_5282_ = v_reuseFailAlloc_5287_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5283_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5283_, 0, v___x_5282_);
                v___x_5284_ = lean_unsigned_to_nat(0);
                v___x_5285_ = 0;
                v___x_5286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_5284_,
                    v___x_5285_,
                    v___x_5283_,
                    v___f_5280_,
                );
                return v___x_5286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed(
    mut v_a_5290_: *mut LeanObject,
    mut v_x_5291_: *mut LeanObject,
    mut v___y_5292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5293_: *mut LeanObject = core::ptr::null_mut();
    v_res_5293_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6(v_a_5290_, v_x_5291_);
    lean_dec(v_a_5290_);
    return v_res_5293_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(
    mut v_a_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: u8 = 0;
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    v___x_5296_ = lean_st_ref_get(v_a_5294_);
    lean_inc(v_a_5294_);
    v___f_5297_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___lam__6___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5297_, 0, v_a_5294_);
    v___x_5298_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5298_, 0, v___x_5296_);
    v___x_5299_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5299_, 0, v___x_5298_);
    v___x_5300_ = lean_unsigned_to_nat(0);
    v___x_5301_ = 0;
    v___x_5302_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5300_,
        v___x_5301_,
        v___x_5299_,
        v___f_5297_,
    );
    return v___x_5302_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1___boxed(
    mut v_a_5303_: *mut LeanObject,
    mut v___y_5304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5305_: *mut LeanObject = core::ptr::null_mut();
    v_res_5305_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v_a_5303_);
    lean_dec(v_a_5303_);
    return v_res_5305_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(
    mut v_mutex_5306_: *mut LeanObject,
    mut v_x_5307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    v___x_5309_ = lean_io_basemutex_unlock(v_mutex_5306_);
    v___x_5310_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5310_, 0, v___x_5309_);
    v___x_5311_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5311_, 0, v___x_5310_);
    return v___x_5311_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed(
    mut v_mutex_5312_: *mut LeanObject,
    mut v_x_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5315_: *mut LeanObject = core::ptr::null_mut();
    v_res_5315_ =
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0(
            v_mutex_5312_,
            v_x_5313_,
        );
    lean_dec(v_x_5313_);
    lean_dec(v_mutex_5312_);
    return v_res_5315_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(
    mut v_k_5316_: *mut LeanObject,
    mut v_ref_5317_: *mut LeanObject,
    mut v_x_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5323_: u8 = 0;
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5318_) == 0 {
                    lean_dec(v_ref_5317_);
                    lean_dec_ref(v_k_5316_);
                    v_a_5320_ = lean_ctor_get(v_x_5318_, 0);
                    v_isSharedCheck_5328_ = (!lean_is_exclusive(v_x_5318_)) as u8;
                    if v_isSharedCheck_5328_ == 0 {
                        v___x_5322_ = v_x_5318_;
                        v_isShared_5323_ = v_isSharedCheck_5328_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5320_);
                        lean_dec(v_x_5318_);
                        v___x_5322_ = lean_box(0);
                        v_isShared_5323_ = v_isSharedCheck_5328_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_5318_, 1);
                    v___x_5329_ = lean_apply_2(v_k_5316_, v_ref_5317_, lean_box(0));
                    return v___x_5329_;
                }
            }
            1 => {
                if v_isShared_5323_ == 0 {
                    v___x_5325_ = v___x_5322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5320_);
                    v___x_5325_ = v_reuseFailAlloc_5327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5326_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5326_, 0, v___x_5325_);
                return v___x_5326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed(
    mut v_k_5330_: *mut LeanObject,
    mut v_ref_5331_: *mut LeanObject,
    mut v_x_5332_: *mut LeanObject,
    mut v___y_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5334_: *mut LeanObject = core::ptr::null_mut();
    v_res_5334_ =
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1(
            v_k_5330_,
            v_ref_5331_,
            v_x_5332_,
        );
    return v_res_5334_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(
    mut v_mutex_5335_: *mut LeanObject,
    mut v___f_5336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: u8 = 0;
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    v___x_5338_ = lean_io_basemutex_lock(v_mutex_5335_);
    v___x_5339_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5339_, 0, v___x_5338_);
    v___x_5340_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5340_, 0, v___x_5339_);
    v___x_5341_ = lean_unsigned_to_nat(0);
    v___x_5342_ = 0;
    v___x_5343_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5341_,
        v___x_5342_,
        v___x_5340_,
        v___f_5336_,
    );
    return v___x_5343_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed(
    mut v_mutex_5344_: *mut LeanObject,
    mut v___f_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5347_: *mut LeanObject = core::ptr::null_mut();
    v_res_5347_ =
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2(
            v_mutex_5344_,
            v___f_5345_,
        );
    lean_dec(v_mutex_5344_);
    return v_res_5347_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__3(
    mut v___y_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_a_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5360_: u8 = 0;
    let mut v_fst_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_5348_) == 0 {
                    v_a_5349_ = lean_ctor_get(v___y_5348_, 0);
                    v_isSharedCheck_5356_ = (!lean_is_exclusive(v___y_5348_)) as u8;
                    if v_isSharedCheck_5356_ == 0 {
                        v___x_5351_ = v___y_5348_;
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5349_);
                        lean_dec(v___y_5348_);
                        v___x_5351_ = lean_box(0);
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5357_ = lean_ctor_get(v___y_5348_, 0);
                    v_isSharedCheck_5365_ = (!lean_is_exclusive(v___y_5348_)) as u8;
                    if v_isSharedCheck_5365_ == 0 {
                        v___x_5359_ = v___y_5348_;
                        v_isShared_5360_ = v_isSharedCheck_5365_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5357_);
                        lean_dec(v___y_5348_);
                        v___x_5359_ = lean_box(0);
                        v_isShared_5360_ = v_isSharedCheck_5365_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5352_ == 0 {
                    v___x_5354_ = v___x_5351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
                    v___x_5354_ = v_reuseFailAlloc_5355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5354_;
            }
            3 => {
                v_fst_5361_ = lean_ctor_get(v_a_5357_, 0);
                lean_inc(v_fst_5361_);
                lean_dec(v_a_5357_);
                if v_isShared_5360_ == 0 {
                    lean_ctor_set(v___x_5359_, 0, v_fst_5361_);
                    v___x_5363_ = v___x_5359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_fst_5361_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
    mut v_mutex_5367_: *mut LeanObject,
    mut v_k_5368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: u8 = 0;
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5385_: u8 = 0;
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5389_: u8 = 0;
    let mut v_a_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5393_: u8 = 0;
    let mut v_fst_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5398_: u8 = 0;
    let mut v_a_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5402_: u8 = 0;
    let mut v___f_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5370_ = lean_ctor_get(v_mutex_5367_, 0);
                lean_inc(v_ref_5370_);
                v_mutex_5371_ = lean_ctor_get(v_mutex_5367_, 1);
                lean_inc_n(v_mutex_5371_, 2);
                lean_dec_ref(v_mutex_5367_);
                v___f_5372_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_5372_, 0, v_mutex_5371_);
                v___f_5373_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_5373_, 0, v_k_5368_);
                lean_closure_set(v___f_5373_, 1, v_ref_5370_);
                v___f_5374_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_5374_, 0, v_mutex_5371_);
                lean_closure_set(v___f_5374_, 1, v___f_5373_);
                v___x_5375_ = lean_unsigned_to_nat(0);
                v___x_5376_ = 0;
                v___x_5377_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_5374_,
                    v___f_5372_,
                    v___x_5375_,
                    v___x_5376_,
                );
                if lean_obj_tag(v___x_5377_) == 0 {
                    v_a_5381_ = lean_ctor_get(v___x_5377_, 0);
                    lean_inc(v_a_5381_);
                    lean_dec_ref_known(v___x_5377_, 1);
                    if lean_obj_tag(v_a_5381_) == 0 {
                        v_a_5382_ = lean_ctor_get(v_a_5381_, 0);
                        v_isSharedCheck_5389_ = (!lean_is_exclusive(v_a_5381_)) as u8;
                        if v_isSharedCheck_5389_ == 0 {
                            v___x_5384_ = v_a_5381_;
                            v_isShared_5385_ = v_isSharedCheck_5389_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5382_);
                            lean_dec(v_a_5381_);
                            v___x_5384_ = lean_box(0);
                            v_isShared_5385_ = v_isSharedCheck_5389_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5390_ = lean_ctor_get(v_a_5381_, 0);
                        v_isSharedCheck_5398_ = (!lean_is_exclusive(v_a_5381_)) as u8;
                        if v_isSharedCheck_5398_ == 0 {
                            v___x_5392_ = v_a_5381_;
                            v_isShared_5393_ = v_isSharedCheck_5398_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5390_);
                            lean_dec(v_a_5381_);
                            v___x_5392_ = lean_box(0);
                            v_isShared_5393_ = v_isSharedCheck_5398_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_5399_ = lean_ctor_get(v___x_5377_, 0);
                    v_isSharedCheck_5408_ = (!lean_is_exclusive(v___x_5377_)) as u8;
                    if v_isSharedCheck_5408_ == 0 {
                        v___x_5401_ = v___x_5377_;
                        v_isShared_5402_ = v_isSharedCheck_5408_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5399_);
                        lean_dec(v___x_5377_);
                        v___x_5401_ = lean_box(0);
                        v_isShared_5402_ = v_isSharedCheck_5408_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5380_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5380_, 0, v___y_5379_);
                return v___x_5380_;
            }
            2 => {
                if v_isShared_5385_ == 0 {
                    v___x_5387_ = v___x_5384_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
                    v___x_5387_ = v_reuseFailAlloc_5388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5379_ = v___x_5387_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_5394_ = lean_ctor_get(v_a_5390_, 0);
                lean_inc(v_fst_5394_);
                lean_dec(v_a_5390_);
                if v_isShared_5393_ == 0 {
                    lean_ctor_set(v___x_5392_, 0, v_fst_5394_);
                    v___x_5396_ = v___x_5392_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_fst_5394_);
                    v___x_5396_ = v_reuseFailAlloc_5397_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5379_ = v___x_5396_;
                state = 1;
                continue;
            }
            6 => {
                v___f_5403_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___closed__0;
                v___x_5404_ = lean_task_map(v___f_5403_, v_a_5399_, v___x_5375_, v___x_5376_);
                if v_isShared_5402_ == 0 {
                    lean_ctor_set(v___x_5401_, 0, v___x_5404_);
                    v___x_5406_ = v___x_5401_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5404_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg___boxed(
    mut v_mutex_5409_: *mut LeanObject,
    mut v_k_5410_: *mut LeanObject,
    mut v___y_5411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5412_: *mut LeanObject = core::ptr::null_mut();
    v_res_5412_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_mutex_5409_,
        v_k_5410_,
    );
    return v_res_5412_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(
    mut v_00_u03b1_5413_: *mut LeanObject,
    mut v_00_u03b2_5414_: *mut LeanObject,
    mut v_mutex_5415_: *mut LeanObject,
    mut v_k_5416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    v___x_5418_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_mutex_5415_,
        v_k_5416_,
    );
    return v___x_5418_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed(
    mut v_00_u03b1_5419_: *mut LeanObject,
    mut v_00_u03b2_5420_: *mut LeanObject,
    mut v_mutex_5421_: *mut LeanObject,
    mut v_k_5422_: *mut LeanObject,
    mut v___y_5423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5424_: *mut LeanObject = core::ptr::null_mut();
    v_res_5424_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2(
        v_00_u03b1_5419_,
        v_00_u03b2_5420_,
        v_mutex_5421_,
        v_k_5422_,
    );
    return v_res_5424_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecv___lam__0(
    mut v___y_5425_: *mut LeanObject,
    mut v_x_5426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5431_: u8 = 0;
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5426_) == 0 {
                    v_a_5428_ = lean_ctor_get(v_x_5426_, 0);
                    v_isSharedCheck_5436_ = (!lean_is_exclusive(v_x_5426_)) as u8;
                    if v_isSharedCheck_5436_ == 0 {
                        v___x_5430_ = v_x_5426_;
                        v_isShared_5431_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5428_);
                        lean_dec(v_x_5426_);
                        v___x_5430_ = lean_box(0);
                        v_isShared_5431_ = v_isSharedCheck_5436_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_5426_, 1);
                    v___x_5437_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_5425_);
                    return v___x_5437_;
                }
            }
            1 => {
                if v_isShared_5431_ == 0 {
                    v___x_5433_ = v___x_5430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5428_);
                    v___x_5433_ = v_reuseFailAlloc_5435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5434_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5434_, 0, v___x_5433_);
                return v___x_5434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecv___lam__0___boxed(
    mut v___y_5438_: *mut LeanObject,
    mut v_x_5439_: *mut LeanObject,
    mut v___y_5440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5441_: *mut LeanObject = core::ptr::null_mut();
    v_res_5441_ = l_Std_Http_Body_Stream_tryRecv___lam__0(v___y_5438_, v_x_5439_);
    lean_dec(v___y_5438_);
    return v_res_5441_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecv___lam__1(
    mut v___y_5442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    v___x_5444_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5442_);
    lean_inc(v___y_5442_);
    v___f_5445_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_tryRecv___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5445_, 0, v___y_5442_);
    v___x_5446_ = lean_unsigned_to_nat(0);
    v___x_5447_ = 0;
    v___x_5448_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5446_,
        v___x_5447_,
        v___x_5444_,
        v___f_5445_,
    );
    return v___x_5448_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecv___lam__1___boxed(
    mut v___y_5449_: *mut LeanObject,
    mut v___y_5450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5451_: *mut LeanObject = core::ptr::null_mut();
    v_res_5451_ = l_Std_Http_Body_Stream_tryRecv___lam__1(v___y_5449_);
    lean_dec(v___y_5449_);
    return v_res_5451_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecv(
    mut v_stream_5453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    v___f_5455_ = l_Std_Http_Body_Stream_tryRecv___closed__0;
    v___x_5456_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_stream_5453_,
        v___f_5455_,
    );
    return v___x_5456_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecv___boxed(
    mut v_stream_5457_: *mut LeanObject,
    mut v_a_5458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5459_: *mut LeanObject = core::ptr::null_mut();
    v_res_5459_ = l_Std_Http_Body_Stream_tryRecv(v_stream_5457_);
    return v_res_5459_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(
    mut v_x_5460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5463_: u8 = 0;
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5470_: u8 = 0;
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5475_: u8 = 0;
    let mut v_a_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5478_: u8 = 0;
    let mut v___x_5479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5460_) == 0 {
                    v_a_5467_ = lean_ctor_get(v_x_5460_, 0);
                    v_isSharedCheck_5475_ = (!lean_is_exclusive(v_x_5460_)) as u8;
                    if v_isSharedCheck_5475_ == 0 {
                        v___x_5469_ = v_x_5460_;
                        v_isShared_5470_ = v_isSharedCheck_5475_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5467_);
                        lean_dec(v_x_5460_);
                        v___x_5469_ = lean_box(0);
                        v_isShared_5470_ = v_isSharedCheck_5475_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5476_ = lean_ctor_get(v_x_5460_, 0);
                    lean_inc(v_a_5476_);
                    lean_dec_ref_known(v_x_5460_, 1);
                    v_pendingProducer_5477_ = lean_ctor_get(v_a_5476_, 0);
                    if lean_obj_tag(v_pendingProducer_5477_) == 0 {
                        v_closed_5478_ = lean_ctor_get_uint8(
                            v_a_5476_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        );
                        lean_dec(v_a_5476_);
                        v___y_5463_ = v_closed_5478_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_5476_);
                        v___x_5479_ = 1;
                        v___y_5463_ = v___x_5479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5464_ = lean_box((v___y_5463_) as usize);
                v___x_5465_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5465_, 0, v___x_5464_);
                v___x_5466_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5466_, 0, v___x_5465_);
                return v___x_5466_;
            }
            2 => {
                if v_isShared_5470_ == 0 {
                    v___x_5472_ = v___x_5469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5467_);
                    v___x_5472_ = v_reuseFailAlloc_5474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5473_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5473_, 0, v___x_5472_);
                return v___x_5473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0___boxed(
    mut v_x_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5482_: *mut LeanObject = core::ptr::null_mut();
    v_res_5482_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___lam__0(v_x_5480_);
    return v_res_5482_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(
    mut v_a_5484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: u8 = 0;
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    v___x_5486_ = lean_st_ref_get(v_a_5484_);
    v___f_5487_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___closed__0;
    v___x_5488_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5488_, 0, v___x_5486_);
    v___x_5489_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5489_, 0, v___x_5488_);
    v___x_5490_ = lean_unsigned_to_nat(0);
    v___x_5491_ = 0;
    v___x_5492_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5490_,
        v___x_5491_,
        v___x_5489_,
        v___f_5487_,
    );
    return v___x_5492_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0___boxed(
    mut v_a_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5495_: *mut LeanObject = core::ptr::null_mut();
    v_res_5495_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v_a_5493_);
    lean_dec(v_a_5493_);
    return v_res_5495_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__0(
    mut v_x_5496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5501_: u8 = 0;
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v_a_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5496_) == 0 {
                    v_a_5498_ = lean_ctor_get(v_x_5496_, 0);
                    v_isSharedCheck_5506_ = (!lean_is_exclusive(v_x_5496_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5500_ = v_x_5496_;
                        v_isShared_5501_ = v_isSharedCheck_5506_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5498_);
                        lean_dec(v_x_5496_);
                        v___x_5500_ = lean_box(0);
                        v_isShared_5501_ = v_isSharedCheck_5506_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5507_ = lean_ctor_get(v_x_5496_, 0);
                    v_isSharedCheck_5516_ = (!lean_is_exclusive(v_x_5496_)) as u8;
                    if v_isSharedCheck_5516_ == 0 {
                        v___x_5509_ = v_x_5496_;
                        v_isShared_5510_ = v_isSharedCheck_5516_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5507_);
                        lean_dec(v_x_5496_);
                        v___x_5509_ = lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5516_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5501_ == 0 {
                    v___x_5503_ = v___x_5500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5498_);
                    v___x_5503_ = v_reuseFailAlloc_5505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5504_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5504_, 0, v___x_5503_);
                return v___x_5504_;
            }
            3 => {
                v___x_5511_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5511_, 0, v_a_5507_);
                if v_isShared_5510_ == 0 {
                    lean_ctor_set(v___x_5509_, 0, v___x_5511_);
                    v___x_5513_ = v___x_5509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5511_);
                    v___x_5513_ = v_reuseFailAlloc_5515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5514_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5514_, 0, v___x_5513_);
                return v___x_5514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__0___boxed(
    mut v_x_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5519_: *mut LeanObject = core::ptr::null_mut();
    v_res_5519_ = l_Std_Http_Body_Stream_tryRecvBody___lam__0(v_x_5517_);
    return v_res_5519_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__1(
    mut v___y_5524_: *mut LeanObject,
    mut v___f_5525_: *mut LeanObject,
    mut v_x_5526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5531_: u8 = 0;
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_a_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: u8 = 0;
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5526_) == 0 {
                    lean_dec_ref(v___f_5525_);
                    v_a_5528_ = lean_ctor_get(v_x_5526_, 0);
                    v_isSharedCheck_5536_ = (!lean_is_exclusive(v_x_5526_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v___x_5530_ = v_x_5526_;
                        v_isShared_5531_ = v_isSharedCheck_5536_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5528_);
                        lean_dec(v_x_5526_);
                        v___x_5530_ = lean_box(0);
                        v_isShared_5531_ = v_isSharedCheck_5536_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5537_ = lean_ctor_get(v_x_5526_, 0);
                    lean_inc(v_a_5537_);
                    lean_dec_ref_known(v_x_5526_, 1);
                    v___x_5538_ = (lean_unbox(v_a_5537_) as u8);
                    lean_dec(v_a_5537_);
                    if v___x_5538_ == 0 {
                        lean_dec_ref(v___f_5525_);
                        v___x_5539_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1___closed__1;
                        return v___x_5539_;
                    } else {
                        v___x_5540_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_5524_);
                        v___x_5541_ = lean_unsigned_to_nat(0);
                        v___x_5542_ = 0;
                        v___x_5543_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_5541_,
                                v___x_5542_,
                                v___x_5540_,
                                v___f_5525_,
                            );
                        return v___x_5543_;
                    }
                }
            }
            1 => {
                if v_isShared_5531_ == 0 {
                    v___x_5533_ = v___x_5530_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5528_);
                    v___x_5533_ = v_reuseFailAlloc_5535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5534_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5534_, 0, v___x_5533_);
                return v___x_5534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed(
    mut v___y_5544_: *mut LeanObject,
    mut v___f_5545_: *mut LeanObject,
    mut v_x_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5548_: *mut LeanObject = core::ptr::null_mut();
    v_res_5548_ = l_Std_Http_Body_Stream_tryRecvBody___lam__1(v___y_5544_, v___f_5545_, v_x_5546_);
    lean_dec(v___y_5544_);
    return v_res_5548_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__2(
    mut v___y_5549_: *mut LeanObject,
    mut v___f_5550_: *mut LeanObject,
    mut v_x_5551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5556_: u8 = 0;
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5561_: u8 = 0;
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: u8 = 0;
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5551_) == 0 {
                    lean_dec_ref(v___f_5550_);
                    v_a_5553_ = lean_ctor_get(v_x_5551_, 0);
                    v_isSharedCheck_5561_ = (!lean_is_exclusive(v_x_5551_)) as u8;
                    if v_isSharedCheck_5561_ == 0 {
                        v___x_5555_ = v_x_5551_;
                        v_isShared_5556_ = v_isSharedCheck_5561_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5553_);
                        lean_dec(v_x_5551_);
                        v___x_5555_ = lean_box(0);
                        v_isShared_5556_ = v_isSharedCheck_5561_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_5551_, 1);
                    v___x_5562_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_5549_);
                    v___x_5563_ = lean_unsigned_to_nat(0);
                    v___x_5564_ = 0;
                    v___x_5565_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_5563_,
                            v___x_5564_,
                            v___x_5562_,
                            v___f_5550_,
                        );
                    return v___x_5565_;
                }
            }
            1 => {
                if v_isShared_5556_ == 0 {
                    v___x_5558_ = v___x_5555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5553_);
                    v___x_5558_ = v_reuseFailAlloc_5560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5559_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5559_, 0, v___x_5558_);
                return v___x_5559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed(
    mut v___y_5566_: *mut LeanObject,
    mut v___f_5567_: *mut LeanObject,
    mut v_x_5568_: *mut LeanObject,
    mut v___y_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5570_: *mut LeanObject = core::ptr::null_mut();
    v_res_5570_ = l_Std_Http_Body_Stream_tryRecvBody___lam__2(v___y_5566_, v___f_5567_, v_x_5568_);
    lean_dec(v___y_5566_);
    return v_res_5570_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__3(
    mut v___f_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: u8 = 0;
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    v___x_5574_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_5572_);
    lean_inc_n(v___y_5572_, 2);
    v___f_5575_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_tryRecvBody___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5575_, 0, v___y_5572_);
    lean_closure_set(v___f_5575_, 1, v___f_5571_);
    v___f_5576_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_tryRecvBody___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5576_, 0, v___y_5572_);
    lean_closure_set(v___f_5576_, 1, v___f_5575_);
    v___x_5577_ = lean_unsigned_to_nat(0);
    v___x_5578_ = 0;
    v___x_5579_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5577_,
        v___x_5578_,
        v___x_5574_,
        v___f_5576_,
    );
    return v___x_5579_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___lam__3___boxed(
    mut v___f_5580_: *mut LeanObject,
    mut v___y_5581_: *mut LeanObject,
    mut v___y_5582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5583_: *mut LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Std_Http_Body_Stream_tryRecvBody___lam__3(v___f_5580_, v___y_5581_);
    lean_dec(v___y_5581_);
    return v_res_5583_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody(
    mut v_stream_5587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    v___f_5589_ = l_Std_Http_Body_Stream_tryRecvBody___closed__1;
    v___x_5590_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_stream_5587_,
        v___f_5589_,
    );
    return v___x_5590_;
}
pub unsafe fn l_Std_Http_Body_Stream_tryRecvBody___boxed(
    mut v_stream_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5593_: *mut LeanObject = core::ptr::null_mut();
    v_res_5593_ = l_Std_Http_Body_Stream_tryRecvBody(v_stream_5591_);
    return v_res_5593_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(
    mut v_a_5594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5600_: u8 = 0;
    let mut v_knownSize_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v___y_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: u8 = 0;
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: u8 = 0;
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = lean_st_ref_get(v_a_5594_);
                v_pendingProducer_5597_ = lean_ctor_get(v___x_5596_, 0);
                v_pendingConsumer_5598_ = lean_ctor_get(v___x_5596_, 1);
                v_interestWaiter_5599_ = lean_ctor_get(v___x_5596_, 2);
                v_closed_5600_ = lean_ctor_get_uint8(
                    v___x_5596_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_knownSize_5601_ = lean_ctor_get(v___x_5596_, 3);
                v_pendingIncompleteChunk_5602_ = lean_ctor_get(v___x_5596_, 4);
                v_isSharedCheck_5628_ = (!lean_is_exclusive(v___x_5596_)) as u8;
                if v_isSharedCheck_5628_ == 0 {
                    v___x_5604_ = v___x_5596_;
                    v_isShared_5605_ = v_isSharedCheck_5628_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pendingIncompleteChunk_5602_);
                    lean_inc(v_knownSize_5601_);
                    lean_inc(v_interestWaiter_5599_);
                    lean_inc(v_pendingConsumer_5598_);
                    lean_inc(v_pendingProducer_5597_);
                    lean_dec(v___x_5596_);
                    v___x_5604_ = lean_box(0);
                    v_isShared_5605_ = v_isSharedCheck_5628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_pendingConsumer_5598_) == 1 {
                    v_val_5622_ = lean_ctor_get(v_pendingConsumer_5598_, 0);
                    if lean_obj_tag(v_val_5622_) == 1 {
                        v_finished_5623_ = lean_ctor_get(v_val_5622_, 0);
                        v_finished_5624_ = lean_ctor_get(v_finished_5623_, 0);
                        v___x_5625_ = lean_st_ref_get(v_finished_5624_);
                        v___x_5626_ = (lean_unbox(v___x_5625_) as u8);
                        lean_dec(v___x_5625_);
                        if v___x_5626_ == 0 {
                            v_pendingConsumer_5615_ = v_pendingConsumer_5598_;
                            v___y_5616_ = v_a_5594_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref_known(v_pendingConsumer_5598_, 1);
                            v___x_5627_ = lean_box(0);
                            v_pendingConsumer_5615_ = v___x_5627_;
                            v___y_5616_ = v_a_5594_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_pendingConsumer_5615_ = v_pendingConsumer_5598_;
                        v___y_5616_ = v_a_5594_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_pendingConsumer_5615_ = v_pendingConsumer_5598_;
                    v___y_5616_ = v_a_5594_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_5605_ == 0 {
                    lean_ctor_set(v___x_5604_, 2, v_interestWaiter_5608_);
                    lean_ctor_set(v___x_5604_, 1, v___y_5607_);
                    v___x_5611_ = v___x_5604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_pendingProducer_5597_);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 1, v___y_5607_);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 2, v_interestWaiter_5608_);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 3, v_knownSize_5601_);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 4, v_pendingIncompleteChunk_5602_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5613_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_5600_,
                    );
                    v___x_5611_ = v_reuseFailAlloc_5613_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5612_ = lean_st_ref_set(v___y_5609_, v___x_5611_);
                return v___x_5612_;
            }
            4 => {
                if lean_obj_tag(v_interestWaiter_5599_) == 0 {
                    v___y_5607_ = v_pendingConsumer_5615_;
                    v_interestWaiter_5608_ = v_interestWaiter_5599_;
                    v___y_5609_ = v___y_5616_;
                    state = 2;
                    continue;
                } else {
                    v_val_5617_ = lean_ctor_get(v_interestWaiter_5599_, 0);
                    v_finished_5618_ = lean_ctor_get(v_val_5617_, 0);
                    v___x_5619_ = lean_st_ref_get(v_finished_5618_);
                    v___x_5620_ = (lean_unbox(v___x_5619_) as u8);
                    lean_dec(v___x_5619_);
                    if v___x_5620_ == 0 {
                        v___y_5607_ = v_pendingConsumer_5615_;
                        v_interestWaiter_5608_ = v_interestWaiter_5599_;
                        v___y_5609_ = v___y_5616_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref_known(v_interestWaiter_5599_, 1);
                        v___x_5621_ = lean_box(0);
                        v___y_5607_ = v_pendingConsumer_5615_;
                        v_interestWaiter_5608_ = v___x_5621_;
                        v___y_5609_ = v___y_5616_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0___boxed(
    mut v_a_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5631_: *mut LeanObject = core::ptr::null_mut();
    v_res_5631_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v_a_5629_);
    lean_dec(v_a_5629_);
    return v_res_5631_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(
    mut v_a_5632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v_pendingConsumer_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5642_: u8 = 0;
    let mut v_knownSize_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v_chunk_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: u8 = 0;
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5662_: u8 = 0;
    let mut v_unused_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5634_ = lean_st_ref_get(v_a_5632_);
                v_pendingProducer_5635_ = lean_ctor_get(v___x_5634_, 0);
                lean_inc(v_pendingProducer_5635_);
                if lean_obj_tag(v_pendingProducer_5635_) == 1 {
                    v_val_5636_ = lean_ctor_get(v_pendingProducer_5635_, 0);
                    v_isSharedCheck_5664_ = (!lean_is_exclusive(v_pendingProducer_5635_)) as u8;
                    if v_isSharedCheck_5664_ == 0 {
                        v___x_5638_ = v_pendingProducer_5635_;
                        v_isShared_5639_ = v_isSharedCheck_5664_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5636_);
                        lean_dec(v_pendingProducer_5635_);
                        v___x_5638_ = lean_box(0);
                        v_isShared_5639_ = v_isSharedCheck_5664_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_pendingProducer_5635_);
                    lean_dec(v___x_5634_);
                    v___x_5665_ = lean_box(0);
                    return v___x_5665_;
                }
            }
            1 => {
                v_pendingConsumer_5640_ = lean_ctor_get(v___x_5634_, 1);
                v_interestWaiter_5641_ = lean_ctor_get(v___x_5634_, 2);
                v_closed_5642_ = lean_ctor_get_uint8(
                    v___x_5634_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_knownSize_5643_ = lean_ctor_get(v___x_5634_, 3);
                v_pendingIncompleteChunk_5644_ = lean_ctor_get(v___x_5634_, 4);
                v_isSharedCheck_5662_ = (!lean_is_exclusive(v___x_5634_)) as u8;
                if v_isSharedCheck_5662_ == 0 {
                    v_unused_5663_ = lean_ctor_get(v___x_5634_, 0);
                    lean_dec(v_unused_5663_);
                    v___x_5646_ = v___x_5634_;
                    v_isShared_5647_ = v_isSharedCheck_5662_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_pendingIncompleteChunk_5644_);
                    lean_inc(v_knownSize_5643_);
                    lean_inc(v_interestWaiter_5641_);
                    lean_inc(v_pendingConsumer_5640_);
                    lean_dec(v___x_5634_);
                    v___x_5646_ = lean_box(0);
                    v_isShared_5647_ = v_isSharedCheck_5662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_chunk_5648_ = lean_ctor_get(v_val_5636_, 0);
                lean_inc_ref(v_chunk_5648_);
                v_done_5649_ = lean_ctor_get(v_val_5636_, 1);
                lean_inc(v_done_5649_);
                lean_dec(v_val_5636_);
                v___x_5650_ = lean_box(0);
                v___x_5651_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_5643_, v_chunk_5648_);
                if v_isShared_5647_ == 0 {
                    lean_ctor_set(v___x_5646_, 3, v___x_5651_);
                    lean_ctor_set(v___x_5646_, 0, v___x_5650_);
                    v___x_5653_ = v___x_5646_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5650_);
                    lean_ctor_set(v_reuseFailAlloc_5661_, 1, v_pendingConsumer_5640_);
                    lean_ctor_set(v_reuseFailAlloc_5661_, 2, v_interestWaiter_5641_);
                    lean_ctor_set(v_reuseFailAlloc_5661_, 3, v___x_5651_);
                    lean_ctor_set(v_reuseFailAlloc_5661_, 4, v_pendingIncompleteChunk_5644_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5661_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_5642_,
                    );
                    v___x_5653_ = v_reuseFailAlloc_5661_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5654_ = lean_st_ref_set(v_a_5632_, v___x_5653_);
                v___x_5655_ = 1;
                v___x_5656_ = lean_box((v___x_5655_) as usize);
                v___x_5657_ = lean_io_promise_resolve(v___x_5656_, v_done_5649_);
                lean_dec(v_done_5649_);
                if v_isShared_5639_ == 0 {
                    lean_ctor_set(v___x_5638_, 0, v_chunk_5648_);
                    v___x_5659_ = v___x_5638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_chunk_5648_);
                    v___x_5659_ = v_reuseFailAlloc_5660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1___boxed(
    mut v_a_5666_: *mut LeanObject,
    mut v___y_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5668_: *mut LeanObject = core::ptr::null_mut();
    v_res_5668_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v_a_5666_);
    lean_dec(v_a_5666_);
    return v_res_5668_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(
    mut v_a_5669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5675_: u8 = 0;
    let mut v_knownSize_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5680_: u8 = 0;
    let mut v_val_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: u8 = 0;
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5689_: u8 = 0;
    let mut v_unused_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5671_ = lean_st_ref_get(v_a_5669_);
                v_interestWaiter_5672_ = lean_ctor_get(v___x_5671_, 2);
                lean_inc(v_interestWaiter_5672_);
                if lean_obj_tag(v_interestWaiter_5672_) == 1 {
                    v_pendingProducer_5673_ = lean_ctor_get(v___x_5671_, 0);
                    v_pendingConsumer_5674_ = lean_ctor_get(v___x_5671_, 1);
                    v_closed_5675_ = lean_ctor_get_uint8(
                        v___x_5671_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_knownSize_5676_ = lean_ctor_get(v___x_5671_, 3);
                    v_pendingIncompleteChunk_5677_ = lean_ctor_get(v___x_5671_, 4);
                    v_isSharedCheck_5689_ = (!lean_is_exclusive(v___x_5671_)) as u8;
                    if v_isSharedCheck_5689_ == 0 {
                        v_unused_5690_ = lean_ctor_get(v___x_5671_, 2);
                        lean_dec(v_unused_5690_);
                        v___x_5679_ = v___x_5671_;
                        v_isShared_5680_ = v_isSharedCheck_5689_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_pendingIncompleteChunk_5677_);
                        lean_inc(v_knownSize_5676_);
                        lean_inc(v_pendingConsumer_5674_);
                        lean_inc(v_pendingProducer_5673_);
                        lean_dec(v___x_5671_);
                        v___x_5679_ = lean_box(0);
                        v_isShared_5680_ = v_isSharedCheck_5689_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_interestWaiter_5672_);
                    lean_dec(v___x_5671_);
                    v___x_5691_ = lean_box(0);
                    return v___x_5691_;
                }
            }
            1 => {
                v_val_5681_ = lean_ctor_get(v_interestWaiter_5672_, 0);
                lean_inc(v_val_5681_);
                lean_dec_ref_known(v_interestWaiter_5672_, 1);
                v___x_5682_ = 1;
                v___x_5683_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_5681_, v___x_5682_);
                lean_dec(v_val_5681_);
                v___x_5684_ = lean_box(0);
                if v_isShared_5680_ == 0 {
                    lean_ctor_set(v___x_5679_, 2, v___x_5684_);
                    v___x_5686_ = v___x_5679_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_pendingProducer_5673_);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 1, v_pendingConsumer_5674_);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 2, v___x_5684_);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 3, v_knownSize_5676_);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 4, v_pendingIncompleteChunk_5677_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5688_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_5675_,
                    );
                    v___x_5686_ = v_reuseFailAlloc_5688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5687_ = lean_st_ref_set(v_a_5669_, v___x_5686_);
                return v___x_5687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2___boxed(
    mut v_a_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5694_: *mut LeanObject = core::ptr::null_mut();
    v_res_5694_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v_a_5692_);
    lean_dec(v_a_5692_);
    return v_res_5694_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(
    mut v_mutex_5695_: *mut LeanObject,
    mut v_k_5696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5698_ = lean_ctor_get(v_mutex_5695_, 0);
    lean_inc(v_ref_5698_);
    v_mutex_5699_ = lean_ctor_get(v_mutex_5695_, 1);
    lean_inc(v_mutex_5699_);
    lean_dec_ref(v_mutex_5695_);
    v___x_5700_ = lean_io_basemutex_lock(v_mutex_5699_);
    v___x_5701_ = lean_apply_2(v_k_5696_, v_ref_5698_, lean_box(0));
    v___x_5702_ = lean_io_basemutex_unlock(v_mutex_5699_);
    lean_dec(v_mutex_5699_);
    return v___x_5701_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg___boxed(
    mut v_mutex_5703_: *mut LeanObject,
    mut v_k_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5706_: *mut LeanObject = core::ptr::null_mut();
    v_res_5706_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_5703_, v_k_5704_);
    return v_res_5706_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(
    mut v_00_u03b1_5707_: *mut LeanObject,
    mut v_00_u03b2_5708_: *mut LeanObject,
    mut v_mutex_5709_: *mut LeanObject,
    mut v_k_5710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    v___x_5712_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_mutex_5709_, v_k_5710_);
    return v___x_5712_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___boxed(
    mut v_00_u03b1_5713_: *mut LeanObject,
    mut v_00_u03b2_5714_: *mut LeanObject,
    mut v_mutex_5715_: *mut LeanObject,
    mut v_k_5716_: *mut LeanObject,
    mut v___y_5717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5718_: *mut LeanObject = core::ptr::null_mut();
    v_res_5718_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3(v_00_u03b1_5713_, v_00_u03b2_5714_, v_mutex_5715_, v_k_5716_);
    return v_res_5718_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0(
    mut v_x_5724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5729_: u8 = 0;
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5724_) == 0 {
                    v___x_5725_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__0___closed__2;
                    return v___x_5725_;
                } else {
                    v_val_5726_ = lean_ctor_get(v_x_5724_, 0);
                    v_isSharedCheck_5733_ = (!lean_is_exclusive(v_x_5724_)) as u8;
                    if v_isSharedCheck_5733_ == 0 {
                        v___x_5728_ = v_x_5724_;
                        v_isShared_5729_ = v_isSharedCheck_5733_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5726_);
                        lean_dec(v_x_5724_);
                        v___x_5728_ = lean_box(0);
                        v_isShared_5729_ = v_isSharedCheck_5733_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5729_ == 0 {
                    v___x_5731_ = v___x_5728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_val_5726_);
                    v___x_5731_ = v_reuseFailAlloc_5732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    v___x_5739_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__2;
    v___x_5740_ = lean_task_pure(v___x_5739_);
    return v___x_5740_;
}
pub unsafe fn _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    v___x_5741_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0;
    v___x_5742_ = lean_task_pure(v___x_5741_);
    return v___x_5742_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(
    mut v___f_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5751_: u8 = 0;
    let mut v_pendingConsumer_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5772_: u8 = 0;
    let mut v_unused_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5746_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_5744_);
                v___x_5747_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__1(v___y_5744_);
                if lean_obj_tag(v___x_5747_) == 1 {
                    lean_dec_ref(v___f_5743_);
                    v___x_5748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5748_, 0, v___x_5747_);
                    v___x_5749_ = lean_task_pure(v___x_5748_);
                    return v___x_5749_;
                } else {
                    lean_dec(v___x_5747_);
                    v___x_5750_ = lean_st_ref_get(v___y_5744_);
                    v_closed_5751_ = lean_ctor_get_uint8(
                        v___x_5750_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    if v_closed_5751_ == 0 {
                        v_pendingConsumer_5752_ = lean_ctor_get(v___x_5750_, 1);
                        lean_inc(v_pendingConsumer_5752_);
                        if lean_obj_tag(v_pendingConsumer_5752_) == 0 {
                            v_pendingProducer_5753_ = lean_ctor_get(v___x_5750_, 0);
                            v_interestWaiter_5754_ = lean_ctor_get(v___x_5750_, 2);
                            v_knownSize_5755_ = lean_ctor_get(v___x_5750_, 3);
                            v_pendingIncompleteChunk_5756_ = lean_ctor_get(v___x_5750_, 4);
                            v_isSharedCheck_5772_ = (!lean_is_exclusive(v___x_5750_)) as u8;
                            if v_isSharedCheck_5772_ == 0 {
                                v_unused_5773_ = lean_ctor_get(v___x_5750_, 1);
                                lean_dec(v_unused_5773_);
                                v___x_5758_ = v___x_5750_;
                                v_isShared_5759_ = v_isSharedCheck_5772_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_pendingIncompleteChunk_5756_);
                                lean_inc(v_knownSize_5755_);
                                lean_inc(v_interestWaiter_5754_);
                                lean_inc(v_pendingProducer_5753_);
                                lean_dec(v___x_5750_);
                                v___x_5758_ = lean_box(0);
                                v_isShared_5759_ = v_isSharedCheck_5772_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_pendingConsumer_5752_, 1);
                            lean_dec(v___x_5750_);
                            lean_dec_ref(v___f_5743_);
                            v___x_5774_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3_once), _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__3);
                            return v___x_5774_;
                        }
                    } else {
                        lean_dec(v___x_5750_);
                        lean_dec_ref(v___f_5743_);
                        v___x_5775_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4_once), _init_l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___closed__4);
                        return v___x_5775_;
                    }
                }
            }
            1 => {
                v___x_5760_ = lean_io_promise_new();
                lean_inc(v___x_5760_);
                v___x_5761_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5761_, 0, v___x_5760_);
                v___x_5762_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5762_, 0, v___x_5761_);
                if v_isShared_5759_ == 0 {
                    lean_ctor_set(v___x_5758_, 1, v___x_5762_);
                    v___x_5764_ = v___x_5758_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_pendingProducer_5753_);
                    lean_ctor_set(v_reuseFailAlloc_5771_, 1, v___x_5762_);
                    lean_ctor_set(v_reuseFailAlloc_5771_, 2, v_interestWaiter_5754_);
                    lean_ctor_set(v_reuseFailAlloc_5771_, 3, v_knownSize_5755_);
                    lean_ctor_set(v_reuseFailAlloc_5771_, 4, v_pendingIncompleteChunk_5756_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5771_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_5751_,
                    );
                    v___x_5764_ = v_reuseFailAlloc_5771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5765_ = lean_st_ref_set(v___y_5744_, v___x_5764_);
                v___x_5766_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__2(v___y_5744_);
                v___x_5767_ = 1;
                v___x_5768_ = lean_io_promise_result_opt(v___x_5760_);
                lean_dec(v___x_5760_);
                v___x_5769_ = lean_unsigned_to_nat(0);
                v___x_5770_ = lean_task_map(v___f_5743_, v___x_5768_, v___x_5769_, v___x_5767_);
                return v___x_5770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1___boxed(
    mut v___f_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5779_: *mut LeanObject = core::ptr::null_mut();
    v_res_5779_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___lam__1(
        v___f_5776_,
        v___y_5777_,
    );
    lean_dec(v___y_5777_);
    return v_res_5779_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(
    mut v_stream_5783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    v___f_5785_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___closed__1;
    v___x_5786_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_5783_, v___f_5785_);
    return v___x_5786_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27___boxed(
    mut v_stream_5787_: *mut LeanObject,
    mut v_a_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5789_: *mut LeanObject = core::ptr::null_mut();
    v_res_5789_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_5787_);
    return v_res_5789_;
}
pub unsafe fn l_Std_Http_Body_Stream_recv___lam__0(
    mut v_x_5790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5800_: u8 = 0;
    let mut v_a_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5790_) == 0 {
                    v_a_5792_ = lean_ctor_get(v_x_5790_, 0);
                    v_isSharedCheck_5800_ = (!lean_is_exclusive(v_x_5790_)) as u8;
                    if v_isSharedCheck_5800_ == 0 {
                        v___x_5794_ = v_x_5790_;
                        v_isShared_5795_ = v_isSharedCheck_5800_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5792_);
                        lean_dec(v_x_5790_);
                        v___x_5794_ = lean_box(0);
                        v_isShared_5795_ = v_isSharedCheck_5800_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5801_ = lean_ctor_get(v_x_5790_, 0);
                    lean_inc(v_a_5801_);
                    lean_dec_ref_known(v_x_5790_, 1);
                    v___x_5802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5802_, 0, v_a_5801_);
                    return v___x_5802_;
                }
            }
            1 => {
                if v_isShared_5795_ == 0 {
                    v___x_5797_ = v___x_5794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_a_5792_);
                    v___x_5797_ = v_reuseFailAlloc_5799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5798_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5798_, 0, v___x_5797_);
                return v___x_5798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_recv___lam__0___boxed(
    mut v_x_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5805_: *mut LeanObject = core::ptr::null_mut();
    v_res_5805_ = l_Std_Http_Body_Stream_recv___lam__0(v_x_5803_);
    return v_res_5805_;
}
pub unsafe fn l_Std_Http_Body_Stream_recv(mut v_stream_5807_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: u8 = 0;
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    v___x_5809_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27(v_stream_5807_);
    v___f_5810_ = l_Std_Http_Body_Stream_recv___closed__0;
    v___x_5811_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5811_, 0, v___x_5809_);
    v___x_5812_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5812_, 0, v___x_5811_);
    v___x_5813_ = lean_unsigned_to_nat(0);
    v___x_5814_ = 0;
    v___x_5815_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5813_,
        v___x_5814_,
        v___x_5812_,
        v___f_5810_,
    );
    return v___x_5815_;
}
pub unsafe fn l_Std_Http_Body_Stream_recv___boxed(
    mut v_stream_5816_: *mut LeanObject,
    mut v_a_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5818_: *mut LeanObject = core::ptr::null_mut();
    v_res_5818_ = l_Std_Http_Body_Stream_recv(v_stream_5816_);
    return v_res_5818_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(
    mut v___x_5819_: u8,
    mut v_knownSize_5820_: *mut LeanObject,
    mut v_____r_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5824_ = lean_box(0);
    v___x_5825_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_5825_, 0, v___x_5824_);
    lean_ctor_set(v___x_5825_, 1, v___x_5824_);
    lean_ctor_set(v___x_5825_, 2, v___x_5824_);
    lean_ctor_set(v___x_5825_, 3, v_knownSize_5820_);
    lean_ctor_set(v___x_5825_, 4, v___x_5824_);
    lean_ctor_set_uint8(
        v___x_5825_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_5819_,
    );
    v___x_5826_ = lean_st_ref_set(v___y_5822_, v___x_5825_);
    v___x_5827_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5827_, 0, v___x_5826_);
    v___x_5828_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5828_, 0, v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed(
    mut v___x_5829_: *mut LeanObject,
    mut v_knownSize_5830_: *mut LeanObject,
    mut v_____r_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
    mut v___y_5833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2149__boxed_5834_: u8 = 0;
    let mut v_res_5835_: *mut LeanObject = core::ptr::null_mut();
    v___x_2149__boxed_5834_ = (lean_unbox(v___x_5829_) as u8);
    v_res_5835_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0(v___x_2149__boxed_5834_, v_knownSize_5830_, v_____r_5831_, v___y_5832_);
    lean_dec(v___y_5832_);
    return v_res_5835_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(
    mut v___f_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v_x_5838_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5838_) == 0 {
        let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_5836_);
        v___x_5840_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5840_, 0, v_x_5838_);
        return v___x_5840_;
    } else {
        let mut v_a_5841_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
        v_a_5841_ = lean_ctor_get(v_x_5838_, 0);
        lean_inc(v_a_5841_);
        lean_dec_ref_known(v_x_5838_, 1);
        lean_inc(v___y_5837_);
        v___x_5842_ = lean_apply_3(v___f_5836_, v_a_5841_, v___y_5837_, lean_box(0));
        return v___x_5842_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed(
    mut v___f_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v_x_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5847_: *mut LeanObject = core::ptr::null_mut();
    v_res_5847_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1(v___f_5843_, v___y_5844_, v_x_5845_);
    lean_dec(v___y_5844_);
    return v_res_5847_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(
    mut v_pendingProducer_5848_: *mut LeanObject,
    mut v_closed_5849_: u8,
    mut v___f_5850_: *mut LeanObject,
    mut v_____r_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_pendingProducer_5848_) == 1 {
        let mut v_val_5854_: *mut LeanObject = core::ptr::null_mut();
        let mut v_done_5855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
        v_val_5854_ = lean_ctor_get(v_pendingProducer_5848_, 0);
        v_done_5855_ = lean_ctor_get(v_val_5854_, 1);
        v___x_5856_ = lean_box((v_closed_5849_) as usize);
        v___x_5857_ = lean_io_promise_resolve(v___x_5856_, v_done_5855_);
        lean_inc(v___y_5852_);
        v___f_5858_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
        lean_closure_set(v___f_5858_, 0, v___f_5850_);
        lean_closure_set(v___f_5858_, 1, v___y_5852_);
        v___x_5859_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
        v___x_5860_ = lean_unsigned_to_nat(0);
        v___x_5861_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_5860_,
            v_closed_5849_,
            v___x_5859_,
            v___f_5858_,
        );
        return v___x_5861_;
    } else {
        let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
        v___x_5862_ = lean_box(0);
        lean_inc(v___y_5852_);
        v___x_5863_ = lean_apply_3(v___f_5850_, v___x_5862_, v___y_5852_, lean_box(0));
        return v___x_5863_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed(
    mut v_pendingProducer_5864_: *mut LeanObject,
    mut v_closed_5865_: *mut LeanObject,
    mut v___f_5866_: *mut LeanObject,
    mut v_____r_5867_: *mut LeanObject,
    mut v___y_5868_: *mut LeanObject,
    mut v___y_5869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_5870_: u8 = 0;
    let mut v_res_5871_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_5870_ = (lean_unbox(v_closed_5865_) as u8);
    v_res_5871_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2(v_pendingProducer_5864_, v_closed_boxed_5870_, v___f_5866_, v_____r_5867_, v___y_5868_);
    lean_dec(v___y_5868_);
    lean_dec(v_pendingProducer_5864_);
    return v_res_5871_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(
    mut v_interestWaiter_5872_: *mut LeanObject,
    mut v_closed_5873_: u8,
    mut v___f_5874_: *mut LeanObject,
    mut v_____r_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_interestWaiter_5872_) == 1 {
        let mut v_val_5878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5879_: u8 = 0;
        let mut v___f_5880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
        v_val_5878_ = lean_ctor_get(v_interestWaiter_5872_, 0);
        v___x_5879_ =
            l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(
                v_val_5878_,
                v_closed_5873_,
            );
        lean_inc(v___y_5876_);
        v___f_5880_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
        lean_closure_set(v___f_5880_, 0, v___f_5874_);
        lean_closure_set(v___f_5880_, 1, v___y_5876_);
        v___x_5881_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
        v___x_5882_ = lean_unsigned_to_nat(0);
        v___x_5883_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_5882_,
            v_closed_5873_,
            v___x_5881_,
            v___f_5880_,
        );
        return v___x_5883_;
    } else {
        let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
        v___x_5884_ = lean_box(0);
        lean_inc(v___y_5876_);
        v___x_5885_ = lean_apply_3(v___f_5874_, v___x_5884_, v___y_5876_, lean_box(0));
        return v___x_5885_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed(
    mut v_interestWaiter_5886_: *mut LeanObject,
    mut v_closed_5887_: *mut LeanObject,
    mut v___f_5888_: *mut LeanObject,
    mut v_____r_5889_: *mut LeanObject,
    mut v___y_5890_: *mut LeanObject,
    mut v___y_5891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_5892_: u8 = 0;
    let mut v_res_5893_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_5892_ = (lean_unbox(v_closed_5887_) as u8);
    v_res_5893_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_5886_, v_closed_boxed_5892_, v___f_5888_, v_____r_5889_, v___y_5890_);
    lean_dec(v___y_5890_);
    lean_dec(v_interestWaiter_5886_);
    return v_res_5893_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(
    mut v___f_5894_: *mut LeanObject,
    mut v_a_5895_: *mut LeanObject,
    mut v_x_5896_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5896_) == 0 {
        let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_5894_);
        v___x_5898_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5898_, 0, v_x_5896_);
        return v___x_5898_;
    } else {
        let mut v_a_5899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
        v_a_5899_ = lean_ctor_get(v_x_5896_, 0);
        lean_inc(v_a_5899_);
        lean_dec_ref_known(v_x_5896_, 1);
        lean_inc(v_a_5895_);
        v___x_5900_ = lean_apply_3(v___f_5894_, v_a_5899_, v_a_5895_, lean_box(0));
        return v___x_5900_;
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed(
    mut v___f_5901_: *mut LeanObject,
    mut v_a_5902_: *mut LeanObject,
    mut v_x_5903_: *mut LeanObject,
    mut v___y_5904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5905_: *mut LeanObject = core::ptr::null_mut();
    v_res_5905_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3(v___f_5901_, v_a_5902_, v_x_5903_);
    lean_dec(v_a_5902_);
    return v_res_5905_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(
    mut v_a_5906_: *mut LeanObject,
    mut v_x_5907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5912_: u8 = 0;
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut v_a_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5919_: u8 = 0;
    let mut v_pendingProducer_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: u8 = 0;
    let mut v___f_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5907_) == 0 {
                    v_a_5909_ = lean_ctor_get(v_x_5907_, 0);
                    v_isSharedCheck_5917_ = (!lean_is_exclusive(v_x_5907_)) as u8;
                    if v_isSharedCheck_5917_ == 0 {
                        v___x_5911_ = v_x_5907_;
                        v_isShared_5912_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5909_);
                        lean_dec(v_x_5907_);
                        v___x_5911_ = lean_box(0);
                        v_isShared_5912_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5918_ = lean_ctor_get(v_x_5907_, 0);
                    lean_inc(v_a_5918_);
                    lean_dec_ref_known(v_x_5907_, 1);
                    v_closed_5919_ = lean_ctor_get_uint8(
                        v_a_5918_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    if v_closed_5919_ == 0 {
                        v_pendingProducer_5920_ = lean_ctor_get(v_a_5918_, 0);
                        lean_inc(v_pendingProducer_5920_);
                        v_pendingConsumer_5921_ = lean_ctor_get(v_a_5918_, 1);
                        lean_inc(v_pendingConsumer_5921_);
                        v_interestWaiter_5922_ = lean_ctor_get(v_a_5918_, 2);
                        lean_inc_n(v_interestWaiter_5922_, 2);
                        v_knownSize_5923_ = lean_ctor_get(v_a_5918_, 3);
                        lean_inc(v_knownSize_5923_);
                        lean_dec(v_a_5918_);
                        v___x_5924_ = 1;
                        v___x_5925_ = lean_box((v___x_5924_) as usize);
                        v___f_5926_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
                        lean_closure_set(v___f_5926_, 0, v___x_5925_);
                        lean_closure_set(v___f_5926_, 1, v_knownSize_5923_);
                        v___x_5927_ = lean_box((v_closed_5919_) as usize);
                        v___f_5928_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                        lean_closure_set(v___f_5928_, 0, v_pendingProducer_5920_);
                        lean_closure_set(v___f_5928_, 1, v___x_5927_);
                        lean_closure_set(v___f_5928_, 2, v___f_5926_);
                        v___x_5929_ = lean_box((v_closed_5919_) as usize);
                        lean_inc_ref(v___f_5928_);
                        v___f_5930_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4___boxed as *mut core::ffi::c_void, 6, 3);
                        lean_closure_set(v___f_5930_, 0, v_interestWaiter_5922_);
                        lean_closure_set(v___f_5930_, 1, v___x_5929_);
                        lean_closure_set(v___f_5930_, 2, v___f_5928_);
                        if lean_obj_tag(v_pendingConsumer_5921_) == 1 {
                            lean_dec_ref(v___f_5928_);
                            lean_dec(v_interestWaiter_5922_);
                            v_val_5931_ = lean_ctor_get(v_pendingConsumer_5921_, 0);
                            lean_inc(v_val_5931_);
                            lean_dec_ref_known(v_pendingConsumer_5921_, 1);
                            v___x_5932_ = lean_box(0);
                            v___x_5933_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(v_val_5931_, v___x_5932_);
                            lean_dec(v_val_5931_);
                            lean_inc(v_a_5906_);
                            v___f_5934_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
                            lean_closure_set(v___f_5934_, 0, v___f_5930_);
                            lean_closure_set(v___f_5934_, 1, v_a_5906_);
                            v___x_5935_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                            v___x_5936_ = lean_unsigned_to_nat(0);
                            v___x_5937_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5936_, v_closed_5919_, v___x_5935_, v___f_5934_);
                            return v___x_5937_;
                        } else {
                            lean_dec_ref(v___f_5930_);
                            lean_dec(v_pendingConsumer_5921_);
                            v___x_5938_ = lean_box(0);
                            v___x_5939_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__4(v_interestWaiter_5922_, v_closed_5919_, v___f_5928_, v___x_5938_, v_a_5906_);
                            lean_dec(v_interestWaiter_5922_);
                            return v___x_5939_;
                        }
                    } else {
                        lean_dec(v_a_5918_);
                        v___x_5940_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                        return v___x_5940_;
                    }
                }
            }
            1 => {
                if v_isShared_5912_ == 0 {
                    v___x_5914_ = v___x_5911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_a_5909_);
                    v___x_5914_ = v_reuseFailAlloc_5916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5915_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5915_, 0, v___x_5914_);
                return v___x_5915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed(
    mut v_a_5941_: *mut LeanObject,
    mut v_x_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5944_: *mut LeanObject = core::ptr::null_mut();
    v_res_5944_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5(v_a_5941_, v_x_5942_);
    lean_dec(v_a_5941_);
    return v_res_5944_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(
    mut v_a_5945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: u8 = 0;
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    v___x_5947_ = lean_st_ref_get(v_a_5945_);
    lean_inc(v_a_5945_);
    v___f_5948_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__5___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5948_, 0, v_a_5945_);
    v___x_5949_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5949_, 0, v___x_5947_);
    v___x_5950_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5950_, 0, v___x_5949_);
    v___x_5951_ = lean_unsigned_to_nat(0);
    v___x_5952_ = 0;
    v___x_5953_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5951_,
        v___x_5952_,
        v___x_5950_,
        v___f_5948_,
    );
    return v___x_5953_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___boxed(
    mut v_a_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5956_: *mut LeanObject = core::ptr::null_mut();
    v_res_5956_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0(v_a_5954_);
    lean_dec(v_a_5954_);
    return v_res_5956_;
}
pub unsafe fn l_Std_Http_Body_Stream_close(mut v_stream_5958_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    v___f_5960_ = l_Std_Http_Body_Stream_close___closed__0;
    v___x_5961_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_stream_5958_,
        v___f_5960_,
    );
    return v___x_5961_;
}
pub unsafe fn l_Std_Http_Body_Stream_close___boxed(
    mut v_stream_5962_: *mut LeanObject,
    mut v_a_5963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5964_: *mut LeanObject = core::ptr::null_mut();
    v_res_5964_ = l_Std_Http_Body_Stream_close(v_stream_5962_);
    return v_res_5964_;
}
pub unsafe fn l_Std_Http_Body_Stream_isClosed___lam__0(
    mut v_____do__lift_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_5968_: u8 = 0;
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    v_closed_5968_ = lean_ctor_get_uint8(
        v_____do__lift_5965_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
    );
    v___x_5969_ = lean_box((v_closed_5968_) as usize);
    v___x_5970_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5970_, 0, v___x_5969_);
    v___x_5971_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5971_, 0, v___x_5970_);
    return v___x_5971_;
}
pub unsafe fn l_Std_Http_Body_Stream_isClosed___lam__0___boxed(
    mut v_____do__lift_5972_: *mut LeanObject,
    mut v___y_5973_: *mut LeanObject,
    mut v___y_5974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5975_: *mut LeanObject = core::ptr::null_mut();
    v_res_5975_ = l_Std_Http_Body_Stream_isClosed___lam__0(v_____do__lift_5972_, v___y_5973_);
    lean_dec(v___y_5973_);
    lean_dec_ref(v_____do__lift_5972_);
    return v_res_5975_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_isClosed___closed__1() -> *mut LeanObject {
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    v___x_5977_ = l_Std_Async_EAsync_instMonad(lean_box(0));
    return v___x_5977_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_isClosed___closed__2() -> *mut LeanObject {
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    v___x_5978_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
    return v___x_5978_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_isClosed___closed__6() -> *mut LeanObject {
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5986_: *mut LeanObject = core::ptr::null_mut();
    v___x_5984_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__2_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__2,
    );
    v___f_5985_ = l_Std_Http_Body_Stream_isClosed___closed__5;
    v___f_5986_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5986_, 0, v___f_5985_);
    lean_closure_set(v___f_5986_, 1, v___x_5984_);
    return v___f_5986_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_isClosed___closed__11() -> *mut LeanObject {
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5997_: *mut LeanObject = core::ptr::null_mut();
    v___x_5995_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__2),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__2_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__2,
    );
    v___f_5996_ = l_Std_Http_Body_Stream_isClosed___closed__10;
    v___f_5997_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_5997_, 0, v___f_5996_);
    lean_closure_set(v___f_5997_, 1, v___x_5995_);
    return v___f_5997_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_isClosed___closed__12() -> *mut LeanObject {
    let mut v___f_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    v___f_5998_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__11),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__11_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__11,
    );
    v___x_5999_ = lean_alloc_closure(l_StateRefT_x27_get___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_5999_, 0, lean_box(0));
    lean_closure_set(v___x_5999_, 1, lean_box(0));
    lean_closure_set(v___x_5999_, 2, lean_box(0));
    lean_closure_set(v___x_5999_, 3, v___f_5998_);
    return v___x_5999_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_isClosed___closed__13() -> *mut LeanObject {
    let mut v___f_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    v___f_6000_ = l_Std_Http_Body_Stream_isClosed___closed__0;
    v___x_6001_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__12),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__12_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__12,
    );
    v___x_6002_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__1,
    );
    v___x_6003_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_6003_, 0, lean_box(0));
    lean_closure_set(v___x_6003_, 1, lean_box(0));
    lean_closure_set(v___x_6003_, 2, lean_box(0));
    lean_closure_set(v___x_6003_, 3, v___x_6002_);
    lean_closure_set(v___x_6003_, 4, lean_box(0));
    lean_closure_set(v___x_6003_, 5, lean_box(0));
    lean_closure_set(v___x_6003_, 6, v___x_6001_);
    lean_closure_set(v___x_6003_, 7, v___f_6000_);
    return v___x_6003_;
}
pub unsafe fn l_Std_Http_Body_Stream_isClosed(
    mut v_stream_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_29__overap_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    v___x_6006_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__1,
    );
    v___f_6007_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__6),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__6_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__6,
    );
    v___f_6008_ = l_Std_Http_Body_Stream_isClosed___closed__7;
    v___x_6009_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__13),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__13_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__13,
    );
    v___x_29__overap_6010_ = l_Std_Mutex_atomically___redArg(
        v___x_6006_,
        v___f_6007_,
        v___f_6008_,
        v_stream_6004_,
        v___x_6009_,
    );
    v___x_6011_ = lean_apply_1(v___x_29__overap_6010_, lean_box(0));
    return v___x_6011_;
}
pub unsafe fn l_Std_Http_Body_Stream_isClosed___boxed(
    mut v_stream_6012_: *mut LeanObject,
    mut v_a_6013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6014_: *mut LeanObject = core::ptr::null_mut();
    v_res_6014_ = l_Std_Http_Body_Stream_isClosed(v_stream_6012_);
    return v_res_6014_;
}
pub unsafe fn l_Std_Http_Body_Stream_getKnownSize___lam__0(
    mut v_____do__lift_6015_: *mut LeanObject,
    mut v___y_6016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_knownSize_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    v_knownSize_6018_ = lean_ctor_get(v_____do__lift_6015_, 3);
    lean_inc(v_knownSize_6018_);
    v___x_6019_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6019_, 0, v_knownSize_6018_);
    v___x_6020_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6020_, 0, v___x_6019_);
    return v___x_6020_;
}
pub unsafe fn l_Std_Http_Body_Stream_getKnownSize___lam__0___boxed(
    mut v_____do__lift_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
    mut v___y_6023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6024_: *mut LeanObject = core::ptr::null_mut();
    v_res_6024_ = l_Std_Http_Body_Stream_getKnownSize___lam__0(v_____do__lift_6021_, v___y_6022_);
    lean_dec(v___y_6022_);
    lean_dec_ref(v_____do__lift_6021_);
    return v_res_6024_;
}
pub unsafe fn _init_l_Std_Http_Body_Stream_getKnownSize___closed__1() -> *mut LeanObject {
    let mut v___f_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    v___f_6026_ = l_Std_Http_Body_Stream_getKnownSize___closed__0;
    v___x_6027_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__12),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__12_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__12,
    );
    v___x_6028_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__1,
    );
    v___x_6029_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_6029_, 0, lean_box(0));
    lean_closure_set(v___x_6029_, 1, lean_box(0));
    lean_closure_set(v___x_6029_, 2, lean_box(0));
    lean_closure_set(v___x_6029_, 3, v___x_6028_);
    lean_closure_set(v___x_6029_, 4, lean_box(0));
    lean_closure_set(v___x_6029_, 5, lean_box(0));
    lean_closure_set(v___x_6029_, 6, v___x_6027_);
    lean_closure_set(v___x_6029_, 7, v___f_6026_);
    return v___x_6029_;
}
pub unsafe fn l_Std_Http_Body_Stream_getKnownSize(
    mut v_stream_6030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_29__overap_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    v___x_6032_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__1,
    );
    v___f_6033_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__6),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__6_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__6,
    );
    v___f_6034_ = l_Std_Http_Body_Stream_isClosed___closed__7;
    v___x_6035_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_getKnownSize___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_getKnownSize___closed__1_once),
        _init_l_Std_Http_Body_Stream_getKnownSize___closed__1,
    );
    v___x_29__overap_6036_ = l_Std_Mutex_atomically___redArg(
        v___x_6032_,
        v___f_6033_,
        v___f_6034_,
        v_stream_6030_,
        v___x_6035_,
    );
    v___x_6037_ = lean_apply_1(v___x_29__overap_6036_, lean_box(0));
    return v___x_6037_;
}
pub unsafe fn l_Std_Http_Body_Stream_getKnownSize___boxed(
    mut v_stream_6038_: *mut LeanObject,
    mut v_a_6039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6040_: *mut LeanObject = core::ptr::null_mut();
    v_res_6040_ = l_Std_Http_Body_Stream_getKnownSize(v_stream_6038_);
    return v_res_6040_;
}
pub unsafe fn l_Std_Http_Body_Stream_setKnownSize___lam__0(
    mut v_size_6041_: *mut LeanObject,
    mut v___y_6042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6048_: u8 = 0;
    let mut v_pendingIncompleteChunk_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6052_: u8 = 0;
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v_unused_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6044_ = lean_st_ref_take(v___y_6042_);
                v_pendingProducer_6045_ = lean_ctor_get(v___x_6044_, 0);
                v_pendingConsumer_6046_ = lean_ctor_get(v___x_6044_, 1);
                v_interestWaiter_6047_ = lean_ctor_get(v___x_6044_, 2);
                v_closed_6048_ = lean_ctor_get_uint8(
                    v___x_6044_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_pendingIncompleteChunk_6049_ = lean_ctor_get(v___x_6044_, 4);
                v_isSharedCheck_6058_ = (!lean_is_exclusive(v___x_6044_)) as u8;
                if v_isSharedCheck_6058_ == 0 {
                    v_unused_6059_ = lean_ctor_get(v___x_6044_, 3);
                    lean_dec(v_unused_6059_);
                    v___x_6051_ = v___x_6044_;
                    v_isShared_6052_ = v_isSharedCheck_6058_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pendingIncompleteChunk_6049_);
                    lean_inc(v_interestWaiter_6047_);
                    lean_inc(v_pendingConsumer_6046_);
                    lean_inc(v_pendingProducer_6045_);
                    lean_dec(v___x_6044_);
                    v___x_6051_ = lean_box(0);
                    v_isShared_6052_ = v_isSharedCheck_6058_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6052_ == 0 {
                    lean_ctor_set(v___x_6051_, 3, v_size_6041_);
                    v___x_6054_ = v___x_6051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_pendingProducer_6045_);
                    lean_ctor_set(v_reuseFailAlloc_6057_, 1, v_pendingConsumer_6046_);
                    lean_ctor_set(v_reuseFailAlloc_6057_, 2, v_interestWaiter_6047_);
                    lean_ctor_set(v_reuseFailAlloc_6057_, 3, v_size_6041_);
                    lean_ctor_set(v_reuseFailAlloc_6057_, 4, v_pendingIncompleteChunk_6049_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6057_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_6048_,
                    );
                    v___x_6054_ = v_reuseFailAlloc_6057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6055_ = lean_st_ref_set(v___y_6042_, v___x_6054_);
                v___x_6056_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                return v___x_6056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed(
    mut v_size_6060_: *mut LeanObject,
    mut v___y_6061_: *mut LeanObject,
    mut v___y_6062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6063_: *mut LeanObject = core::ptr::null_mut();
    v_res_6063_ = l_Std_Http_Body_Stream_setKnownSize___lam__0(v_size_6060_, v___y_6061_);
    lean_dec(v___y_6061_);
    return v_res_6063_;
}
pub unsafe fn l_Std_Http_Body_Stream_setKnownSize(
    mut v_stream_6064_: *mut LeanObject,
    mut v_size_6065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_25__overap_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    v___f_6067_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_setKnownSize___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6067_, 0, v_size_6065_);
    v___x_6068_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__1_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__1,
    );
    v___f_6069_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__6),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Stream_isClosed___closed__6_once),
        _init_l_Std_Http_Body_Stream_isClosed___closed__6,
    );
    v___f_6070_ = l_Std_Http_Body_Stream_isClosed___closed__7;
    v___x_25__overap_6071_ = l_Std_Mutex_atomically___redArg(
        v___x_6068_,
        v___f_6069_,
        v___f_6070_,
        v_stream_6064_,
        v___f_6067_,
    );
    v___x_6072_ = lean_apply_1(v___x_25__overap_6071_, lean_box(0));
    return v___x_6072_;
}
pub unsafe fn l_Std_Http_Body_Stream_setKnownSize___boxed(
    mut v_stream_6073_: *mut LeanObject,
    mut v_size_6074_: *mut LeanObject,
    mut v_a_6075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6076_: *mut LeanObject = core::ptr::null_mut();
    v_res_6076_ = l_Std_Http_Body_Stream_setKnownSize(v_stream_6073_, v_size_6074_);
    return v_res_6076_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(
    mut v_pendingProducer_6077_: *mut LeanObject,
    mut v_pendingConsumer_6078_: *mut LeanObject,
    mut v_closed_6079_: u8,
    mut v_knownSize_6080_: *mut LeanObject,
    mut v_pendingIncompleteChunk_6081_: *mut LeanObject,
    mut v_a_6082_: *mut LeanObject,
    mut v_x_6083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6088_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6096_: u8 = 0;
    let mut v_unused_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6083_) == 0 {
                    lean_dec(v_pendingIncompleteChunk_6081_);
                    lean_dec(v_knownSize_6080_);
                    lean_dec(v_pendingConsumer_6078_);
                    lean_dec(v_pendingProducer_6077_);
                    v___x_6085_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6085_, 0, v_x_6083_);
                    return v___x_6085_;
                } else {
                    v_isSharedCheck_6096_ = (!lean_is_exclusive(v_x_6083_)) as u8;
                    if v_isSharedCheck_6096_ == 0 {
                        v_unused_6097_ = lean_ctor_get(v_x_6083_, 0);
                        lean_dec(v_unused_6097_);
                        v___x_6087_ = v_x_6083_;
                        v_isShared_6088_ = v_isSharedCheck_6096_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_6083_);
                        v___x_6087_ = lean_box(0);
                        v_isShared_6088_ = v_isSharedCheck_6096_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6089_ = lean_box(0);
                v___x_6090_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_6090_, 0, v_pendingProducer_6077_);
                lean_ctor_set(v___x_6090_, 1, v_pendingConsumer_6078_);
                lean_ctor_set(v___x_6090_, 2, v___x_6089_);
                lean_ctor_set(v___x_6090_, 3, v_knownSize_6080_);
                lean_ctor_set(v___x_6090_, 4, v_pendingIncompleteChunk_6081_);
                lean_ctor_set_uint8(
                    v___x_6090_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v_closed_6079_,
                );
                v___x_6091_ = lean_st_ref_set(v_a_6082_, v___x_6090_);
                if v_isShared_6088_ == 0 {
                    lean_ctor_set(v___x_6087_, 0, v___x_6091_);
                    v___x_6093_ = v___x_6087_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6095_, 0, v___x_6091_);
                    v___x_6093_ = v_reuseFailAlloc_6095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6094_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6094_, 0, v___x_6093_);
                return v___x_6094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed(
    mut v_pendingProducer_6098_: *mut LeanObject,
    mut v_pendingConsumer_6099_: *mut LeanObject,
    mut v_closed_6100_: *mut LeanObject,
    mut v_knownSize_6101_: *mut LeanObject,
    mut v_pendingIncompleteChunk_6102_: *mut LeanObject,
    mut v_a_6103_: *mut LeanObject,
    mut v_x_6104_: *mut LeanObject,
    mut v___y_6105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_6106_: u8 = 0;
    let mut v_res_6107_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_6106_ = (lean_unbox(v_closed_6100_) as u8);
    v_res_6107_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0(v_pendingProducer_6098_, v_pendingConsumer_6099_, v_closed_boxed_6106_, v_knownSize_6101_, v_pendingIncompleteChunk_6102_, v_a_6103_, v_x_6104_);
    lean_dec(v_a_6103_);
    return v_res_6107_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(
    mut v_a_6108_: *mut LeanObject,
    mut v_x_6109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_a_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6124_: u8 = 0;
    let mut v_knownSize_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: u8 = 0;
    let mut v___x_6129_: u8 = 0;
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6109_) == 0 {
                    v_a_6111_ = lean_ctor_get(v_x_6109_, 0);
                    v_isSharedCheck_6119_ = (!lean_is_exclusive(v_x_6109_)) as u8;
                    if v_isSharedCheck_6119_ == 0 {
                        v___x_6113_ = v_x_6109_;
                        v_isShared_6114_ = v_isSharedCheck_6119_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6111_);
                        lean_dec(v_x_6109_);
                        v___x_6113_ = lean_box(0);
                        v_isShared_6114_ = v_isSharedCheck_6119_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6120_ = lean_ctor_get(v_x_6109_, 0);
                    lean_inc(v_a_6120_);
                    lean_dec_ref_known(v_x_6109_, 1);
                    v_interestWaiter_6121_ = lean_ctor_get(v_a_6120_, 2);
                    lean_inc(v_interestWaiter_6121_);
                    if lean_obj_tag(v_interestWaiter_6121_) == 1 {
                        v_pendingProducer_6122_ = lean_ctor_get(v_a_6120_, 0);
                        lean_inc(v_pendingProducer_6122_);
                        v_pendingConsumer_6123_ = lean_ctor_get(v_a_6120_, 1);
                        lean_inc(v_pendingConsumer_6123_);
                        v_closed_6124_ = lean_ctor_get_uint8(
                            v_a_6120_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        );
                        v_knownSize_6125_ = lean_ctor_get(v_a_6120_, 3);
                        lean_inc(v_knownSize_6125_);
                        v_pendingIncompleteChunk_6126_ = lean_ctor_get(v_a_6120_, 4);
                        lean_inc(v_pendingIncompleteChunk_6126_);
                        lean_dec(v_a_6120_);
                        v_val_6127_ = lean_ctor_get(v_interestWaiter_6121_, 0);
                        lean_inc(v_val_6127_);
                        lean_dec_ref_known(v_interestWaiter_6121_, 1);
                        v___x_6128_ = 1;
                        v___x_6129_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_resolveInterestWaiter(v_val_6127_, v___x_6128_);
                        lean_dec(v_val_6127_);
                        v___x_6130_ = lean_box((v_closed_6124_) as usize);
                        lean_inc(v_a_6108_);
                        v___f_6131_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__0___boxed as *mut core::ffi::c_void, 8, 6);
                        lean_closure_set(v___f_6131_, 0, v_pendingProducer_6122_);
                        lean_closure_set(v___f_6131_, 1, v_pendingConsumer_6123_);
                        lean_closure_set(v___f_6131_, 2, v___x_6130_);
                        lean_closure_set(v___f_6131_, 3, v_knownSize_6125_);
                        lean_closure_set(v___f_6131_, 4, v_pendingIncompleteChunk_6126_);
                        lean_closure_set(v___f_6131_, 5, v_a_6108_);
                        v___x_6132_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                        v___x_6133_ = lean_unsigned_to_nat(0);
                        v___x_6134_ = 0;
                        v___x_6135_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_6133_,
                                v___x_6134_,
                                v___x_6132_,
                                v___f_6131_,
                            );
                        return v___x_6135_;
                    } else {
                        lean_dec(v_interestWaiter_6121_);
                        lean_dec(v_a_6120_);
                        v___x_6136_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                        return v___x_6136_;
                    }
                }
            }
            1 => {
                if v_isShared_6114_ == 0 {
                    v___x_6116_ = v___x_6113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6118_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_a_6111_);
                    v___x_6116_ = v_reuseFailAlloc_6118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6117_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6117_, 0, v___x_6116_);
                return v___x_6117_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed(
    mut v_a_6137_: *mut LeanObject,
    mut v_x_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6140_: *mut LeanObject = core::ptr::null_mut();
    v_res_6140_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1(v_a_6137_, v_x_6138_);
    lean_dec(v_a_6137_);
    return v_res_6140_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(
    mut v_a_6141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: u8 = 0;
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    v___x_6143_ = lean_st_ref_get(v_a_6141_);
    lean_inc(v_a_6141_);
    v___f_6144_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_6144_, 0, v_a_6141_);
    v___x_6145_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6145_, 0, v___x_6143_);
    v___x_6146_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6146_, 0, v___x_6145_);
    v___x_6147_ = lean_unsigned_to_nat(0);
    v___x_6148_ = 0;
    v___x_6149_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6147_,
        v___x_6148_,
        v___x_6146_,
        v___f_6144_,
    );
    return v___x_6149_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0___boxed(
    mut v_a_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6152_: *mut LeanObject = core::ptr::null_mut();
    v_res_6152_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v_a_6150_);
    lean_dec(v_a_6150_);
    return v_res_6152_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(
    mut v_promise_6153_: *mut LeanObject,
    mut v_x_6154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6164_: u8 = 0;
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6154_) == 0 {
                    v_a_6156_ = lean_ctor_get(v_x_6154_, 0);
                    v_isSharedCheck_6164_ = (!lean_is_exclusive(v_x_6154_)) as u8;
                    if v_isSharedCheck_6164_ == 0 {
                        v___x_6158_ = v_x_6154_;
                        v_isShared_6159_ = v_isSharedCheck_6164_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6156_);
                        lean_dec(v_x_6154_);
                        v___x_6158_ = lean_box(0);
                        v_isShared_6159_ = v_isSharedCheck_6164_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6165_ = lean_io_promise_resolve(v_x_6154_, v_promise_6153_);
                    v___x_6166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6166_, 0, v___x_6165_);
                    v___x_6167_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6167_, 0, v___x_6166_);
                    return v___x_6167_;
                }
            }
            1 => {
                if v_isShared_6159_ == 0 {
                    v___x_6161_ = v___x_6158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6156_);
                    v___x_6161_ = v_reuseFailAlloc_6163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6162_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6162_, 0, v___x_6161_);
                return v___x_6162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed(
    mut v_promise_6168_: *mut LeanObject,
    mut v_x_6169_: *mut LeanObject,
    mut v___y_6170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6171_: *mut LeanObject = core::ptr::null_mut();
    v_res_6171_ =
        l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0(
            v_promise_6168_,
            v_x_6169_,
        );
    lean_dec(v_promise_6168_);
    return v_res_6171_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(
    mut v_lose_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
    mut v___f_6174_: *mut LeanObject,
    mut v_x_6175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut v_a_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: u8 = 0;
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: u8 = 0;
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6175_) == 0 {
                    lean_dec_ref(v___f_6174_);
                    lean_dec_ref(v_lose_6172_);
                    v_a_6177_ = lean_ctor_get(v_x_6175_, 0);
                    v_isSharedCheck_6185_ = (!lean_is_exclusive(v_x_6175_)) as u8;
                    if v_isSharedCheck_6185_ == 0 {
                        v___x_6179_ = v_x_6175_;
                        v_isShared_6180_ = v_isSharedCheck_6185_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6177_);
                        lean_dec(v_x_6175_);
                        v___x_6179_ = lean_box(0);
                        v_isShared_6180_ = v_isSharedCheck_6185_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6186_ = lean_ctor_get(v_x_6175_, 0);
                    lean_inc(v_a_6186_);
                    lean_dec_ref_known(v_x_6175_, 1);
                    v___x_6187_ = (lean_unbox(v_a_6186_) as u8);
                    lean_dec(v_a_6186_);
                    if v___x_6187_ == 0 {
                        lean_dec_ref(v___f_6174_);
                        lean_inc(v___y_6173_);
                        v___x_6188_ = lean_apply_2(v_lose_6172_, v___y_6173_, lean_box(0));
                        return v___x_6188_;
                    } else {
                        lean_dec_ref(v_lose_6172_);
                        v___x_6189_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0(v___y_6173_);
                        v___x_6190_ = lean_unsigned_to_nat(0);
                        v___x_6191_ = 0;
                        v___x_6192_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_6190_,
                                v___x_6191_,
                                v___x_6189_,
                                v___f_6174_,
                            );
                        return v___x_6192_;
                    }
                }
            }
            1 => {
                if v_isShared_6180_ == 0 {
                    v___x_6182_ = v___x_6179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6184_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_a_6177_);
                    v___x_6182_ = v_reuseFailAlloc_6184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6183_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6183_, 0, v___x_6182_);
                return v___x_6183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed(
    mut v_lose_6193_: *mut LeanObject,
    mut v___y_6194_: *mut LeanObject,
    mut v___f_6195_: *mut LeanObject,
    mut v_x_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6198_: *mut LeanObject = core::ptr::null_mut();
    v_res_6198_ =
        l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1(
            v_lose_6193_,
            v___y_6194_,
            v___f_6195_,
            v_x_6196_,
        );
    lean_dec(v___y_6194_);
    return v_res_6198_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(
    mut v_w_6199_: *mut LeanObject,
    mut v_lose_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: u8 = 0;
    let mut v___x_6210_: u8 = 0;
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: u8 = 0;
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    let mut v___x_6220_: u8 = 0;
    let mut v___x_6221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_6203_ = lean_ctor_get(v_w_6199_, 0);
                lean_inc(v_finished_6203_);
                v_promise_6204_ = lean_ctor_get(v_w_6199_, 1);
                lean_inc(v_promise_6204_);
                lean_dec_ref(v_w_6199_);
                v___x_6205_ = lean_st_ref_take(v_finished_6203_);
                v___f_6206_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_6206_, 0, v_promise_6204_);
                lean_inc(v___y_6201_);
                v___f_6207_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
                lean_closure_set(v___f_6207_, 0, v_lose_6200_);
                lean_closure_set(v___f_6207_, 1, v___y_6201_);
                lean_closure_set(v___f_6207_, 2, v___f_6206_);
                v___x_6219_ = (lean_unbox(v___x_6205_) as u8);
                lean_dec(v___x_6205_);
                if v___x_6219_ == 0 {
                    v___x_6220_ = 1;
                    v___y_6209_ = v___x_6220_;
                    state = 1;
                    continue;
                } else {
                    v___x_6221_ = 0;
                    v___y_6209_ = v___x_6221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6210_ = 1;
                v___x_6211_ = lean_box((v___x_6210_) as usize);
                v___x_6212_ = lean_st_ref_set(v_finished_6203_, v___x_6211_);
                lean_dec(v_finished_6203_);
                v___x_6213_ = lean_box((v___y_6209_) as usize);
                v___x_6214_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6214_, 0, v___x_6213_);
                v___x_6215_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6215_, 0, v___x_6214_);
                v___x_6216_ = lean_unsigned_to_nat(0);
                v___x_6217_ = 0;
                v___x_6218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_6216_,
                    v___x_6217_,
                    v___x_6215_,
                    v___f_6207_,
                );
                return v___x_6218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1___boxed(
    mut v_w_6222_: *mut LeanObject,
    mut v_lose_6223_: *mut LeanObject,
    mut v___y_6224_: *mut LeanObject,
    mut v___y_6225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6226_: *mut LeanObject = core::ptr::null_mut();
    v_res_6226_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(
        v_w_6222_,
        v_lose_6223_,
        v___y_6224_,
    );
    lean_dec(v___y_6224_);
    return v_res_6226_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__1(
    mut v___y_6227_: *mut LeanObject,
    mut v_x_6228_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6228_) == 0 {
        let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
        v___x_6230_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6230_, 0, v_x_6228_);
        return v___x_6230_;
    } else {
        let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_x_6228_, 1);
        v___x_6231_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_signalInterest___at___00Std_Http_Body_Stream_recvSelector_spec__0(v___y_6227_);
        return v___x_6231_;
    }
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__1___boxed(
    mut v___y_6232_: *mut LeanObject,
    mut v_x_6233_: *mut LeanObject,
    mut v___y_6234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6235_: *mut LeanObject = core::ptr::null_mut();
    v_res_6235_ = l_Std_Http_Body_Stream_recvSelector___lam__1(v___y_6232_, v_x_6233_);
    lean_dec(v___y_6232_);
    return v_res_6235_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__0(
    mut v_waiter_6236_: *mut LeanObject,
    mut v_pendingProducer_6237_: *mut LeanObject,
    mut v_interestWaiter_6238_: *mut LeanObject,
    mut v_closed_6239_: u8,
    mut v_knownSize_6240_: *mut LeanObject,
    mut v_pendingIncompleteChunk_6241_: *mut LeanObject,
    mut v_a_6242_: u8,
    mut v_____r_6243_: *mut LeanObject,
    mut v___y_6244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    v___x_6246_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6246_, 0, v_waiter_6236_);
    v___x_6247_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6247_, 0, v___x_6246_);
    v___x_6248_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_6248_, 0, v_pendingProducer_6237_);
    lean_ctor_set(v___x_6248_, 1, v___x_6247_);
    lean_ctor_set(v___x_6248_, 2, v_interestWaiter_6238_);
    lean_ctor_set(v___x_6248_, 3, v_knownSize_6240_);
    lean_ctor_set(v___x_6248_, 4, v_pendingIncompleteChunk_6241_);
    lean_ctor_set_uint8(
        v___x_6248_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v_closed_6239_,
    );
    v___x_6249_ = lean_st_ref_set(v___y_6244_, v___x_6248_);
    lean_inc(v___y_6244_);
    v___f_6250_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_recvSelector___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6250_, 0, v___y_6244_);
    v___x_6251_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6251_, 0, v___x_6249_);
    v___x_6252_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6252_, 0, v___x_6251_);
    v___x_6253_ = lean_unsigned_to_nat(0);
    v___x_6254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6253_,
        v_a_6242_,
        v___x_6252_,
        v___f_6250_,
    );
    return v___x_6254_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__0___boxed(
    mut v_waiter_6255_: *mut LeanObject,
    mut v_pendingProducer_6256_: *mut LeanObject,
    mut v_interestWaiter_6257_: *mut LeanObject,
    mut v_closed_6258_: *mut LeanObject,
    mut v_knownSize_6259_: *mut LeanObject,
    mut v_pendingIncompleteChunk_6260_: *mut LeanObject,
    mut v_a_6261_: *mut LeanObject,
    mut v_____r_6262_: *mut LeanObject,
    mut v___y_6263_: *mut LeanObject,
    mut v___y_6264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_6265_: u8 = 0;
    let mut v_a_6061__boxed_6266_: u8 = 0;
    let mut v_res_6267_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_6265_ = (lean_unbox(v_closed_6258_) as u8);
    v_a_6061__boxed_6266_ = (lean_unbox(v_a_6261_) as u8);
    v_res_6267_ = l_Std_Http_Body_Stream_recvSelector___lam__0(
        v_waiter_6255_,
        v_pendingProducer_6256_,
        v_interestWaiter_6257_,
        v_closed_boxed_6265_,
        v_knownSize_6259_,
        v_pendingIncompleteChunk_6260_,
        v_a_6061__boxed_6266_,
        v_____r_6262_,
        v___y_6263_,
    );
    lean_dec(v___y_6263_);
    return v_res_6267_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__3(
    mut v_waiter_6272_: *mut LeanObject,
    mut v_a_6273_: u8,
    mut v___y_6274_: *mut LeanObject,
    mut v_x_6275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6280_: u8 = 0;
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6285_: u8 = 0;
    let mut v_a_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6290_: u8 = 0;
    let mut v_knownSize_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6275_) == 0 {
                    lean_dec_ref(v_waiter_6272_);
                    v_a_6277_ = lean_ctor_get(v_x_6275_, 0);
                    v_isSharedCheck_6285_ = (!lean_is_exclusive(v_x_6275_)) as u8;
                    if v_isSharedCheck_6285_ == 0 {
                        v___x_6279_ = v_x_6275_;
                        v_isShared_6280_ = v_isSharedCheck_6285_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6277_);
                        lean_dec(v_x_6275_);
                        v___x_6279_ = lean_box(0);
                        v_isShared_6280_ = v_isSharedCheck_6285_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6286_ = lean_ctor_get(v_x_6275_, 0);
                    lean_inc(v_a_6286_);
                    lean_dec_ref_known(v_x_6275_, 1);
                    v_pendingProducer_6287_ = lean_ctor_get(v_a_6286_, 0);
                    lean_inc_n(v_pendingProducer_6287_, 2);
                    v_pendingConsumer_6288_ = lean_ctor_get(v_a_6286_, 1);
                    lean_inc(v_pendingConsumer_6288_);
                    v_interestWaiter_6289_ = lean_ctor_get(v_a_6286_, 2);
                    lean_inc_n(v_interestWaiter_6289_, 2);
                    v_closed_6290_ = lean_ctor_get_uint8(
                        v_a_6286_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_knownSize_6291_ = lean_ctor_get(v_a_6286_, 3);
                    lean_inc_n(v_knownSize_6291_, 2);
                    v_pendingIncompleteChunk_6292_ = lean_ctor_get(v_a_6286_, 4);
                    lean_inc_n(v_pendingIncompleteChunk_6292_, 2);
                    lean_dec(v_a_6286_);
                    v___x_6293_ = lean_box((v_closed_6290_) as usize);
                    v___x_6294_ = lean_box((v_a_6273_) as usize);
                    lean_inc_ref(v_waiter_6272_);
                    v___f_6295_ = lean_alloc_closure(
                        l_Std_Http_Body_Stream_recvSelector___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        7,
                    );
                    lean_closure_set(v___f_6295_, 0, v_waiter_6272_);
                    lean_closure_set(v___f_6295_, 1, v_pendingProducer_6287_);
                    lean_closure_set(v___f_6295_, 2, v_interestWaiter_6289_);
                    lean_closure_set(v___f_6295_, 3, v___x_6293_);
                    lean_closure_set(v___f_6295_, 4, v_knownSize_6291_);
                    lean_closure_set(v___f_6295_, 5, v_pendingIncompleteChunk_6292_);
                    lean_closure_set(v___f_6295_, 6, v___x_6294_);
                    if lean_obj_tag(v_pendingConsumer_6288_) == 0 {
                        lean_dec_ref(v___f_6295_);
                        v___x_6296_ = lean_box(0);
                        v___x_6297_ = l_Std_Http_Body_Stream_recvSelector___lam__0(
                            v_waiter_6272_,
                            v_pendingProducer_6287_,
                            v_interestWaiter_6289_,
                            v_closed_6290_,
                            v_knownSize_6291_,
                            v_pendingIncompleteChunk_6292_,
                            v_a_6273_,
                            v___x_6296_,
                            v___y_6274_,
                        );
                        return v___x_6297_;
                    } else {
                        lean_dec_ref_known(v_pendingConsumer_6288_, 1);
                        lean_dec(v_pendingIncompleteChunk_6292_);
                        lean_dec(v_knownSize_6291_);
                        lean_dec(v_interestWaiter_6289_);
                        lean_dec(v_pendingProducer_6287_);
                        lean_dec_ref(v_waiter_6272_);
                        lean_inc(v___y_6274_);
                        v___f_6298_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_close_x27___at___00Std_Http_Body_Stream_close_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                        lean_closure_set(v___f_6298_, 0, v___f_6295_);
                        lean_closure_set(v___f_6298_, 1, v___y_6274_);
                        v___x_6299_ = l_Std_Http_Body_Stream_recvSelector___lam__3___closed__1;
                        v___x_6300_ = lean_unsigned_to_nat(0);
                        v___x_6301_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_6300_,
                                v_a_6273_,
                                v___x_6299_,
                                v___f_6298_,
                            );
                        return v___x_6301_;
                    }
                }
            }
            1 => {
                if v_isShared_6280_ == 0 {
                    v___x_6282_ = v___x_6279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6284_, 0, v_a_6277_);
                    v___x_6282_ = v_reuseFailAlloc_6284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6283_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6283_, 0, v___x_6282_);
                return v___x_6283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__3___boxed(
    mut v_waiter_6302_: *mut LeanObject,
    mut v_a_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
    mut v_x_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6102__boxed_6307_: u8 = 0;
    let mut v_res_6308_: *mut LeanObject = core::ptr::null_mut();
    v_a_6102__boxed_6307_ = (lean_unbox(v_a_6303_) as u8);
    v_res_6308_ = l_Std_Http_Body_Stream_recvSelector___lam__3(
        v_waiter_6302_,
        v_a_6102__boxed_6307_,
        v___y_6304_,
        v_x_6305_,
    );
    lean_dec(v___y_6304_);
    return v_res_6308_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__2(
    mut v___x_6309_: *mut LeanObject,
    mut v___y_6310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    v___x_6312_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6312_, 0, v___x_6309_);
    v___x_6313_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6313_, 0, v___x_6312_);
    return v___x_6313_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__2___boxed(
    mut v___x_6314_: *mut LeanObject,
    mut v___y_6315_: *mut LeanObject,
    mut v___y_6316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6317_: *mut LeanObject = core::ptr::null_mut();
    v_res_6317_ = l_Std_Http_Body_Stream_recvSelector___lam__2(v___x_6314_, v___y_6315_);
    lean_dec(v___y_6315_);
    return v_res_6317_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__4(
    mut v___y_6320_: *mut LeanObject,
    mut v_waiter_6321_: *mut LeanObject,
    mut v_x_6322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6327_: u8 = 0;
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6332_: u8 = 0;
    let mut v_a_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v___x_6337_: u8 = 0;
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: u8 = 0;
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6322_) == 0 {
                    lean_dec_ref(v_waiter_6321_);
                    v_a_6324_ = lean_ctor_get(v_x_6322_, 0);
                    v_isSharedCheck_6332_ = (!lean_is_exclusive(v_x_6322_)) as u8;
                    if v_isSharedCheck_6332_ == 0 {
                        v___x_6326_ = v_x_6322_;
                        v_isShared_6327_ = v_isSharedCheck_6332_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6324_);
                        lean_dec(v_x_6322_);
                        v___x_6326_ = lean_box(0);
                        v_isShared_6327_ = v_isSharedCheck_6332_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6333_ = lean_ctor_get(v_x_6322_, 0);
                    v_isSharedCheck_6349_ = (!lean_is_exclusive(v_x_6322_)) as u8;
                    if v_isSharedCheck_6349_ == 0 {
                        v___x_6335_ = v_x_6322_;
                        v_isShared_6336_ = v_isSharedCheck_6349_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6333_);
                        lean_dec(v_x_6322_);
                        v___x_6335_ = lean_box(0);
                        v_isShared_6336_ = v_isSharedCheck_6349_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6327_ == 0 {
                    v___x_6329_ = v___x_6326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6331_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6331_, 0, v_a_6324_);
                    v___x_6329_ = v_reuseFailAlloc_6331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6330_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6330_, 0, v___x_6329_);
                return v___x_6330_;
            }
            3 => {
                v___x_6337_ = (lean_unbox(v_a_6333_) as u8);
                if v___x_6337_ == 0 {
                    v___x_6338_ = lean_st_ref_get(v___y_6320_);
                    lean_inc(v___y_6320_);
                    lean_inc(v_a_6333_);
                    v___f_6339_ = lean_alloc_closure(
                        l_Std_Http_Body_Stream_recvSelector___lam__3___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_6339_, 0, v_waiter_6321_);
                    lean_closure_set(v___f_6339_, 1, v_a_6333_);
                    lean_closure_set(v___f_6339_, 2, v___y_6320_);
                    if v_isShared_6336_ == 0 {
                        lean_ctor_set(v___x_6335_, 0, v___x_6338_);
                        v___x_6341_ = v___x_6335_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6346_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6346_, 0, v___x_6338_);
                        v___x_6341_ = v_reuseFailAlloc_6346_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6335_);
                    lean_dec(v_a_6333_);
                    v___f_6347_ = l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0;
                    v___x_6348_ =
                        l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_recvSelector_spec__1(
                            v_waiter_6321_,
                            v___f_6347_,
                            v___y_6320_,
                        );
                    return v___x_6348_;
                }
            }
            4 => {
                v___x_6342_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6342_, 0, v___x_6341_);
                v___x_6343_ = lean_unsigned_to_nat(0);
                v___x_6344_ = (lean_unbox(v_a_6333_) as u8);
                lean_dec(v_a_6333_);
                v___x_6345_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_6343_,
                    v___x_6344_,
                    v___x_6342_,
                    v___f_6339_,
                );
                return v___x_6345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__4___boxed(
    mut v___y_6350_: *mut LeanObject,
    mut v_waiter_6351_: *mut LeanObject,
    mut v_x_6352_: *mut LeanObject,
    mut v___y_6353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6354_: *mut LeanObject = core::ptr::null_mut();
    v_res_6354_ =
        l_Std_Http_Body_Stream_recvSelector___lam__4(v___y_6350_, v_waiter_6351_, v_x_6352_);
    lean_dec(v___y_6350_);
    return v_res_6354_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__5(
    mut v___y_6355_: *mut LeanObject,
    mut v___f_6356_: *mut LeanObject,
    mut v_x_6357_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6357_) == 0 {
        let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_6356_);
        v___x_6359_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6359_, 0, v_x_6357_);
        return v___x_6359_;
    } else {
        let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6362_: u8 = 0;
        let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_x_6357_, 1);
        v___x_6360_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_recvReady_x27___at___00Std_Http_Body_Stream_tryRecvBody_spec__0(v___y_6355_);
        v___x_6361_ = lean_unsigned_to_nat(0);
        v___x_6362_ = 0;
        v___x_6363_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_6361_,
            v___x_6362_,
            v___x_6360_,
            v___f_6356_,
        );
        return v___x_6363_;
    }
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__5___boxed(
    mut v___y_6364_: *mut LeanObject,
    mut v___f_6365_: *mut LeanObject,
    mut v_x_6366_: *mut LeanObject,
    mut v___y_6367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6368_: *mut LeanObject = core::ptr::null_mut();
    v_res_6368_ = l_Std_Http_Body_Stream_recvSelector___lam__5(v___y_6364_, v___f_6365_, v_x_6366_);
    lean_dec(v___y_6364_);
    return v_res_6368_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__6(
    mut v_waiter_6369_: *mut LeanObject,
    mut v___y_6370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: u8 = 0;
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    v___x_6372_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_6370_);
    lean_inc_n(v___y_6370_, 2);
    v___f_6373_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_recvSelector___lam__4___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_6373_, 0, v___y_6370_);
    lean_closure_set(v___f_6373_, 1, v_waiter_6369_);
    v___f_6374_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_recvSelector___lam__5___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_6374_, 0, v___y_6370_);
    lean_closure_set(v___f_6374_, 1, v___f_6373_);
    v___x_6375_ = lean_unsigned_to_nat(0);
    v___x_6376_ = 0;
    v___x_6377_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6375_,
        v___x_6376_,
        v___x_6372_,
        v___f_6374_,
    );
    return v___x_6377_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__6___boxed(
    mut v_waiter_6378_: *mut LeanObject,
    mut v___y_6379_: *mut LeanObject,
    mut v___y_6380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6381_: *mut LeanObject = core::ptr::null_mut();
    v_res_6381_ = l_Std_Http_Body_Stream_recvSelector___lam__6(v_waiter_6378_, v___y_6379_);
    lean_dec(v___y_6379_);
    return v_res_6381_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__7(
    mut v_stream_6382_: *mut LeanObject,
    mut v_waiter_6383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    v___f_6385_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_recvSelector___lam__6___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6385_, 0, v_waiter_6383_);
    v___x_6386_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_stream_6382_,
        v___f_6385_,
    );
    return v___x_6386_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector___lam__7___boxed(
    mut v_stream_6387_: *mut LeanObject,
    mut v_waiter_6388_: *mut LeanObject,
    mut v___y_6389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6390_: *mut LeanObject = core::ptr::null_mut();
    v_res_6390_ = l_Std_Http_Body_Stream_recvSelector___lam__7(v_stream_6387_, v_waiter_6388_);
    return v_res_6390_;
}
pub unsafe fn l_Std_Http_Body_Stream_recvSelector(
    mut v_stream_6392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    v___f_6393_ = l_Std_Http_Body_Stream_recvSelector___closed__0;
    lean_inc_ref_n(v_stream_6392_, 2);
    v___f_6394_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_recvSelector___lam__7___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6394_, 0, v_stream_6392_);
    v___f_6395_ = l_Std_Http_Body_Stream_tryRecvBody___closed__1;
    v___x_6396_ = lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_6396_, 0, lean_box(0));
    lean_closure_set(v___x_6396_, 1, lean_box(0));
    lean_closure_set(v___x_6396_, 2, v_stream_6392_);
    lean_closure_set(v___x_6396_, 3, v___f_6395_);
    v___x_6397_ = lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_6397_, 0, lean_box(0));
    lean_closure_set(v___x_6397_, 1, lean_box(0));
    lean_closure_set(v___x_6397_, 2, v_stream_6392_);
    lean_closure_set(v___x_6397_, 3, v___f_6393_);
    v___x_6398_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6398_, 0, v___x_6396_);
    lean_ctor_set(v___x_6398_, 1, v___f_6394_);
    lean_ctor_set(v___x_6398_, 2, v___x_6397_);
    return v___x_6398_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(
    mut v_step_6399_: *mut LeanObject,
    mut v_acc_6400_: *mut LeanObject,
    mut v___f_6401_: *mut LeanObject,
    mut v_x_6402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6407_: u8 = 0;
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6412_: u8 = 0;
    let mut v_a_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6416_: u8 = 0;
    let mut v_val_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6402_) == 0 {
                    lean_dec_ref(v___f_6401_);
                    lean_dec(v_acc_6400_);
                    lean_dec_ref(v_step_6399_);
                    v_a_6404_ = lean_ctor_get(v_x_6402_, 0);
                    v_isSharedCheck_6412_ = (!lean_is_exclusive(v_x_6402_)) as u8;
                    if v_isSharedCheck_6412_ == 0 {
                        v___x_6406_ = v_x_6402_;
                        v_isShared_6407_ = v_isSharedCheck_6412_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6404_);
                        lean_dec(v_x_6402_);
                        v___x_6406_ = lean_box(0);
                        v_isShared_6407_ = v_isSharedCheck_6412_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6413_ = lean_ctor_get(v_x_6402_, 0);
                    v_isSharedCheck_6426_ = (!lean_is_exclusive(v_x_6402_)) as u8;
                    if v_isSharedCheck_6426_ == 0 {
                        v___x_6415_ = v_x_6402_;
                        v_isShared_6416_ = v_isSharedCheck_6426_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6413_);
                        lean_dec(v_x_6402_);
                        v___x_6415_ = lean_box(0);
                        v_isShared_6416_ = v_isSharedCheck_6426_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6407_ == 0 {
                    v___x_6409_ = v___x_6406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6411_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_a_6404_);
                    v___x_6409_ = v_reuseFailAlloc_6411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6410_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6410_, 0, v___x_6409_);
                return v___x_6410_;
            }
            3 => {
                if lean_obj_tag(v_a_6413_) == 1 {
                    lean_del_object(v___x_6415_);
                    v_val_6417_ = lean_ctor_get(v_a_6413_, 0);
                    lean_inc(v_val_6417_);
                    lean_dec_ref_known(v_a_6413_, 1);
                    v___x_6418_ = lean_apply_3(v_step_6399_, v_val_6417_, v_acc_6400_, lean_box(0));
                    v___x_6419_ = lean_unsigned_to_nat(0);
                    v___x_6420_ = 0;
                    v___x_6421_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_6419_,
                            v___x_6420_,
                            v___x_6418_,
                            v___f_6401_,
                        );
                    return v___x_6421_;
                } else {
                    lean_dec(v_a_6413_);
                    lean_dec_ref(v___f_6401_);
                    lean_dec_ref(v_step_6399_);
                    if v_isShared_6416_ == 0 {
                        lean_ctor_set(v___x_6415_, 0, v_acc_6400_);
                        v___x_6423_ = v___x_6415_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6425_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_acc_6400_);
                        v___x_6423_ = v_reuseFailAlloc_6425_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6424_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6424_, 0, v___x_6423_);
                return v___x_6424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed(
    mut v_step_6427_: *mut LeanObject,
    mut v_acc_6428_: *mut LeanObject,
    mut v___f_6429_: *mut LeanObject,
    mut v_x_6430_: *mut LeanObject,
    mut v___y_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6432_: *mut LeanObject = core::ptr::null_mut();
    v_res_6432_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1(
            v_step_6427_,
            v_acc_6428_,
            v___f_6429_,
            v_x_6430_,
        );
    return v_res_6432_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(
    mut v_step_6433_: *mut LeanObject,
    mut v_stream_6434_: *mut LeanObject,
    mut v_x_6435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6440_: u8 = 0;
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6445_: u8 = 0;
    let mut v_a_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6449_: u8 = 0;
    let mut v_a_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6453_: u8 = 0;
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6460_: u8 = 0;
    let mut v_a_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6435_) == 0 {
                    lean_dec_ref(v_stream_6434_);
                    lean_dec_ref(v_step_6433_);
                    v_a_6437_ = lean_ctor_get(v_x_6435_, 0);
                    v_isSharedCheck_6445_ = (!lean_is_exclusive(v_x_6435_)) as u8;
                    if v_isSharedCheck_6445_ == 0 {
                        v___x_6439_ = v_x_6435_;
                        v_isShared_6440_ = v_isSharedCheck_6445_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6437_);
                        lean_dec(v_x_6435_);
                        v___x_6439_ = lean_box(0);
                        v_isShared_6440_ = v_isSharedCheck_6445_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6446_ = lean_ctor_get(v_x_6435_, 0);
                    v_isSharedCheck_6463_ = (!lean_is_exclusive(v_x_6435_)) as u8;
                    if v_isSharedCheck_6463_ == 0 {
                        v___x_6448_ = v_x_6435_;
                        v_isShared_6449_ = v_isSharedCheck_6463_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6446_);
                        lean_dec(v_x_6435_);
                        v___x_6448_ = lean_box(0);
                        v_isShared_6449_ = v_isSharedCheck_6463_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6440_ == 0 {
                    v___x_6442_ = v___x_6439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6444_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6437_);
                    v___x_6442_ = v_reuseFailAlloc_6444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6443_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6443_, 0, v___x_6442_);
                return v___x_6443_;
            }
            3 => {
                if lean_obj_tag(v_a_6446_) == 0 {
                    lean_dec_ref(v_stream_6434_);
                    lean_dec_ref(v_step_6433_);
                    v_a_6450_ = lean_ctor_get(v_a_6446_, 0);
                    v_isSharedCheck_6460_ = (!lean_is_exclusive(v_a_6446_)) as u8;
                    if v_isSharedCheck_6460_ == 0 {
                        v___x_6452_ = v_a_6446_;
                        v_isShared_6453_ = v_isSharedCheck_6460_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6450_);
                        lean_dec(v_a_6446_);
                        v___x_6452_ = lean_box(0);
                        v_isShared_6453_ = v_isSharedCheck_6460_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6448_);
                    v_a_6461_ = lean_ctor_get(v_a_6446_, 0);
                    lean_inc(v_a_6461_);
                    lean_dec_ref_known(v_a_6446_, 1);
                    v___x_6462_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(v_step_6433_, v_stream_6434_, v_a_6461_);
                    return v___x_6462_;
                }
            }
            4 => {
                if v_isShared_6449_ == 0 {
                    lean_ctor_set(v___x_6448_, 0, v_a_6450_);
                    v___x_6455_ = v___x_6448_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6450_);
                    v___x_6455_ = v_reuseFailAlloc_6459_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6453_ == 0 {
                    lean_ctor_set(v___x_6452_, 0, v___x_6455_);
                    v___x_6457_ = v___x_6452_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6458_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6458_, 0, v___x_6455_);
                    v___x_6457_ = v_reuseFailAlloc_6458_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed(
    mut v_step_6464_: *mut LeanObject,
    mut v_stream_6465_: *mut LeanObject,
    mut v_x_6466_: *mut LeanObject,
    mut v___y_6467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6468_: *mut LeanObject = core::ptr::null_mut();
    v_res_6468_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0(
            v_step_6464_,
            v_stream_6465_,
            v_x_6466_,
        );
    return v_res_6468_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(
    mut v_step_6469_: *mut LeanObject,
    mut v_stream_6470_: *mut LeanObject,
    mut v_acc_6471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_stream_6470_);
    v___x_6473_ = l_Std_Http_Body_Stream_recv(v_stream_6470_);
    lean_inc_ref(v_step_6469_);
    v___f_6474_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_6474_, 0, v_step_6469_);
    lean_closure_set(v___f_6474_, 1, v_stream_6470_);
    v___f_6475_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___f_6475_, 0, v_step_6469_);
    lean_closure_set(v___f_6475_, 1, v_acc_6471_);
    lean_closure_set(v___f_6475_, 2, v___f_6474_);
    v___x_6476_ = lean_unsigned_to_nat(0);
    v___x_6477_ = 0;
    v___x_6478_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6476_,
        v___x_6477_,
        v___x_6473_,
        v___f_6475_,
    );
    return v___x_6478_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg___boxed(
    mut v_step_6479_: *mut LeanObject,
    mut v_stream_6480_: *mut LeanObject,
    mut v_acc_6481_: *mut LeanObject,
    mut v_a_6482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6483_: *mut LeanObject = core::ptr::null_mut();
    v_res_6483_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(
        v_step_6479_,
        v_stream_6480_,
        v_acc_6481_,
    );
    return v_res_6483_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(
    mut v_00_u03b2_6484_: *mut LeanObject,
    mut v_step_6485_: *mut LeanObject,
    mut v_stream_6486_: *mut LeanObject,
    mut v_acc_6487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    v___x_6489_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(
        v_step_6485_,
        v_stream_6486_,
        v_acc_6487_,
    );
    return v___x_6489_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___boxed(
    mut v_00_u03b2_6490_: *mut LeanObject,
    mut v_step_6491_: *mut LeanObject,
    mut v_stream_6492_: *mut LeanObject,
    mut v_acc_6493_: *mut LeanObject,
    mut v_a_6494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6495_: *mut LeanObject = core::ptr::null_mut();
    v_res_6495_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop(
        v_00_u03b2_6490_,
        v_step_6491_,
        v_stream_6492_,
        v_acc_6493_,
    );
    return v_res_6495_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn___redArg(
    mut v_stream_6496_: *mut LeanObject,
    mut v_acc_6497_: *mut LeanObject,
    mut v_step_6498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    v___x_6500_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(
        v_step_6498_,
        v_stream_6496_,
        v_acc_6497_,
    );
    return v___x_6500_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn___redArg___boxed(
    mut v_stream_6501_: *mut LeanObject,
    mut v_acc_6502_: *mut LeanObject,
    mut v_step_6503_: *mut LeanObject,
    mut v_a_6504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6505_: *mut LeanObject = core::ptr::null_mut();
    v_res_6505_ = l_Std_Http_Body_Stream_forIn___redArg(v_stream_6501_, v_acc_6502_, v_step_6503_);
    return v_res_6505_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn(
    mut v_00_u03b2_6506_: *mut LeanObject,
    mut v_stream_6507_: *mut LeanObject,
    mut v_acc_6508_: *mut LeanObject,
    mut v_step_6509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    v___x_6511_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_loop___redArg(
        v_step_6509_,
        v_stream_6507_,
        v_acc_6508_,
    );
    return v___x_6511_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn___boxed(
    mut v_00_u03b2_6512_: *mut LeanObject,
    mut v_stream_6513_: *mut LeanObject,
    mut v_acc_6514_: *mut LeanObject,
    mut v_step_6515_: *mut LeanObject,
    mut v_a_6516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6517_: *mut LeanObject = core::ptr::null_mut();
    v_res_6517_ =
        l_Std_Http_Body_Stream_forIn(v_00_u03b2_6512_, v_stream_6513_, v_acc_6514_, v_step_6515_);
    return v_res_6517_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(
    mut v_x_6518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6523_: u8 = 0;
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_a_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v_token_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6518_) == 0 {
                    v_a_6520_ = lean_ctor_get(v_x_6518_, 0);
                    v_isSharedCheck_6528_ = (!lean_is_exclusive(v_x_6518_)) as u8;
                    if v_isSharedCheck_6528_ == 0 {
                        v___x_6522_ = v_x_6518_;
                        v_isShared_6523_ = v_isSharedCheck_6528_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6520_);
                        lean_dec(v_x_6518_);
                        v___x_6522_ = lean_box(0);
                        v_isShared_6523_ = v_isSharedCheck_6528_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6529_ = lean_ctor_get(v_x_6518_, 0);
                    v_isSharedCheck_6539_ = (!lean_is_exclusive(v_x_6518_)) as u8;
                    if v_isSharedCheck_6539_ == 0 {
                        v___x_6531_ = v_x_6518_;
                        v_isShared_6532_ = v_isSharedCheck_6539_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6529_);
                        lean_dec(v_x_6518_);
                        v___x_6531_ = lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6539_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6523_ == 0 {
                    v___x_6525_ = v___x_6522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6527_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6520_);
                    v___x_6525_ = v_reuseFailAlloc_6527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6526_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6526_, 0, v___x_6525_);
                return v___x_6526_;
            }
            3 => {
                v_token_6533_ = lean_ctor_get(v_a_6529_, 1);
                lean_inc_ref(v_token_6533_);
                lean_dec(v_a_6529_);
                v___x_6534_ = l_Std_CancellationToken_selector(v_token_6533_);
                if v_isShared_6532_ == 0 {
                    lean_ctor_set(v___x_6531_, 0, v___x_6534_);
                    v___x_6536_ = v___x_6531_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6538_, 0, v___x_6534_);
                    v___x_6536_ = v_reuseFailAlloc_6538_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6537_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6537_, 0, v___x_6536_);
                return v___x_6537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0___boxed(
    mut v_x_6540_: *mut LeanObject,
    mut v___y_6541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6542_: *mut LeanObject = core::ptr::null_mut();
    v_res_6542_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__0(v_x_6540_);
    return v_res_6542_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(
    mut v___y_6543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    v___x_6545_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6545_, 0, v___y_6543_);
    v___x_6546_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6546_, 0, v___x_6545_);
    return v___x_6546_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1___boxed(
    mut v___y_6547_: *mut LeanObject,
    mut v___y_6548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6549_: *mut LeanObject = core::ptr::null_mut();
    v_res_6549_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__1(v___y_6547_);
    return v_res_6549_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(
    mut v_x_6550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    v___x_6552_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1;
    return v___x_6552_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2___boxed(
    mut v_x_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6555_: *mut LeanObject = core::ptr::null_mut();
    v_res_6555_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__2(v_x_6553_);
    return v_res_6555_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(
    mut v_stream_6556_: *mut LeanObject,
    mut v___f_6557_: *mut LeanObject,
    mut v___f_6558_: *mut LeanObject,
    mut v___f_6559_: *mut LeanObject,
    mut v_x_6560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6565_: u8 = 0;
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6570_: u8 = 0;
    let mut v_a_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: u8 = 0;
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6560_) == 0 {
                    lean_dec_ref(v___f_6559_);
                    lean_dec_ref(v___f_6558_);
                    lean_dec_ref(v___f_6557_);
                    lean_dec_ref(v_stream_6556_);
                    v_a_6562_ = lean_ctor_get(v_x_6560_, 0);
                    v_isSharedCheck_6570_ = (!lean_is_exclusive(v_x_6560_)) as u8;
                    if v_isSharedCheck_6570_ == 0 {
                        v___x_6564_ = v_x_6560_;
                        v_isShared_6565_ = v_isSharedCheck_6570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6562_);
                        lean_dec(v_x_6560_);
                        v___x_6564_ = lean_box(0);
                        v_isShared_6565_ = v_isSharedCheck_6570_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6571_ = lean_ctor_get(v_x_6560_, 0);
                    lean_inc(v_a_6571_);
                    lean_dec_ref_known(v_x_6560_, 1);
                    v___x_6572_ = l_Std_Http_Body_Stream_recvSelector(v_stream_6556_);
                    v___x_6573_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6573_, 0, v___x_6572_);
                    lean_ctor_set(v___x_6573_, 1, v___f_6557_);
                    v___x_6574_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6574_, 0, v_a_6571_);
                    lean_ctor_set(v___x_6574_, 1, v___f_6558_);
                    v___x_6575_ = lean_unsigned_to_nat(2);
                    v___x_6576_ = lean_mk_empty_array_with_capacity(v___x_6575_);
                    v___x_6577_ = lean_array_push(v___x_6576_, v___x_6573_);
                    v___x_6578_ = lean_array_push(v___x_6577_, v___x_6574_);
                    v___x_6579_ = l_Std_Async_Selectable_one___redArg(v___x_6578_);
                    v___x_6580_ = lean_unsigned_to_nat(0);
                    v___x_6581_ = 0;
                    v___x_6582_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_6580_,
                            v___x_6581_,
                            v___x_6579_,
                            v___f_6559_,
                        );
                    return v___x_6582_;
                }
            }
            1 => {
                if v_isShared_6565_ == 0 {
                    v___x_6567_ = v___x_6564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6569_, 0, v_a_6562_);
                    v___x_6567_ = v_reuseFailAlloc_6569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6568_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6568_, 0, v___x_6567_);
                return v___x_6568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed(
    mut v_stream_6583_: *mut LeanObject,
    mut v___f_6584_: *mut LeanObject,
    mut v___f_6585_: *mut LeanObject,
    mut v___f_6586_: *mut LeanObject,
    mut v_x_6587_: *mut LeanObject,
    mut v___y_6588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6589_: *mut LeanObject = core::ptr::null_mut();
    v_res_6589_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5(v_stream_6583_, v___f_6584_, v___f_6585_, v___f_6586_, v_x_6587_);
    return v_res_6589_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(
    mut v_step_6590_: *mut LeanObject,
    mut v_acc_6591_: *mut LeanObject,
    mut v_a_6592_: *mut LeanObject,
    mut v___f_6593_: *mut LeanObject,
    mut v_x_6594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6604_: u8 = 0;
    let mut v_a_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6608_: u8 = 0;
    let mut v_val_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: u8 = 0;
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6594_) == 0 {
                    lean_dec_ref(v___f_6593_);
                    lean_dec(v_acc_6591_);
                    lean_dec_ref(v_step_6590_);
                    v_a_6596_ = lean_ctor_get(v_x_6594_, 0);
                    v_isSharedCheck_6604_ = (!lean_is_exclusive(v_x_6594_)) as u8;
                    if v_isSharedCheck_6604_ == 0 {
                        v___x_6598_ = v_x_6594_;
                        v_isShared_6599_ = v_isSharedCheck_6604_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6596_);
                        lean_dec(v_x_6594_);
                        v___x_6598_ = lean_box(0);
                        v_isShared_6599_ = v_isSharedCheck_6604_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6605_ = lean_ctor_get(v_x_6594_, 0);
                    v_isSharedCheck_6618_ = (!lean_is_exclusive(v_x_6594_)) as u8;
                    if v_isSharedCheck_6618_ == 0 {
                        v___x_6607_ = v_x_6594_;
                        v_isShared_6608_ = v_isSharedCheck_6618_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6605_);
                        lean_dec(v_x_6594_);
                        v___x_6607_ = lean_box(0);
                        v_isShared_6608_ = v_isSharedCheck_6618_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6599_ == 0 {
                    v___x_6601_ = v___x_6598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6603_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6603_, 0, v_a_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6603_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6602_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6602_, 0, v___x_6601_);
                return v___x_6602_;
            }
            3 => {
                if lean_obj_tag(v_a_6605_) == 1 {
                    lean_del_object(v___x_6607_);
                    v_val_6609_ = lean_ctor_get(v_a_6605_, 0);
                    lean_inc(v_val_6609_);
                    lean_dec_ref_known(v_a_6605_, 1);
                    lean_inc_ref(v_a_6592_);
                    v___x_6610_ = lean_apply_4(
                        v_step_6590_,
                        v_val_6609_,
                        v_acc_6591_,
                        v_a_6592_,
                        lean_box(0),
                    );
                    v___x_6611_ = lean_unsigned_to_nat(0);
                    v___x_6612_ = 0;
                    v___x_6613_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_6611_,
                            v___x_6612_,
                            v___x_6610_,
                            v___f_6593_,
                        );
                    return v___x_6613_;
                } else {
                    lean_dec(v_a_6605_);
                    lean_dec_ref(v___f_6593_);
                    lean_dec_ref(v_step_6590_);
                    if v_isShared_6608_ == 0 {
                        lean_ctor_set(v___x_6607_, 0, v_acc_6591_);
                        v___x_6615_ = v___x_6607_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6617_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6617_, 0, v_acc_6591_);
                        v___x_6615_ = v_reuseFailAlloc_6617_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6616_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6616_, 0, v___x_6615_);
                return v___x_6616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed(
    mut v_step_6619_: *mut LeanObject,
    mut v_acc_6620_: *mut LeanObject,
    mut v_a_6621_: *mut LeanObject,
    mut v___f_6622_: *mut LeanObject,
    mut v_x_6623_: *mut LeanObject,
    mut v___y_6624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6625_: *mut LeanObject = core::ptr::null_mut();
    v_res_6625_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4(v_step_6619_, v_acc_6620_, v_a_6621_, v___f_6622_, v_x_6623_);
    lean_dec_ref(v_a_6621_);
    return v_res_6625_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed(
    mut v_step_6629_: *mut LeanObject,
    mut v_stream_6630_: *mut LeanObject,
    mut v_a_6631_: *mut LeanObject,
    mut v_x_6632_: *mut LeanObject,
    mut v___y_6633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6634_: *mut LeanObject = core::ptr::null_mut();
    v_res_6634_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(v_step_6629_, v_stream_6630_, v_a_6631_, v_x_6632_);
    lean_dec_ref(v_a_6631_);
    return v_res_6634_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(
    mut v_step_6635_: *mut LeanObject,
    mut v_stream_6636_: *mut LeanObject,
    mut v_acc_6637_: *mut LeanObject,
    mut v_a_6638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: u8 = 0;
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    v___f_6640_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__0;
    lean_inc_ref_n(v_a_6638_, 3);
    v___x_6641_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6641_, 0, v_a_6638_);
    v___x_6642_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6642_, 0, v___x_6641_);
    v___x_6643_ = lean_unsigned_to_nat(0);
    v___x_6644_ = 0;
    v___x_6645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6643_,
        v___x_6644_,
        v___x_6642_,
        v___f_6640_,
    );
    v___f_6646_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__1;
    v___f_6647_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___closed__2;
    lean_inc_ref(v_stream_6636_);
    lean_inc_ref(v_step_6635_);
    v___f_6648_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___f_6648_, 0, v_step_6635_);
    lean_closure_set(v___f_6648_, 1, v_stream_6636_);
    lean_closure_set(v___f_6648_, 2, v_a_6638_);
    v___f_6649_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___f_6649_, 0, v_step_6635_);
    lean_closure_set(v___f_6649_, 1, v_acc_6637_);
    lean_closure_set(v___f_6649_, 2, v_a_6638_);
    lean_closure_set(v___f_6649_, 3, v___f_6648_);
    v___f_6650_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__5___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___f_6650_, 0, v_stream_6636_);
    lean_closure_set(v___f_6650_, 1, v___f_6646_);
    lean_closure_set(v___f_6650_, 2, v___f_6647_);
    lean_closure_set(v___f_6650_, 3, v___f_6649_);
    v___x_6651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6643_,
        v___x_6644_,
        v___x_6645_,
        v___f_6650_,
    );
    return v___x_6651_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___lam__3(
    mut v_step_6652_: *mut LeanObject,
    mut v_stream_6653_: *mut LeanObject,
    mut v_a_6654_: *mut LeanObject,
    mut v_x_6655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6660_: u8 = 0;
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6665_: u8 = 0;
    let mut v_a_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6669_: u8 = 0;
    let mut v_a_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6673_: u8 = 0;
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6680_: u8 = 0;
    let mut v_a_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6655_) == 0 {
                    lean_dec_ref(v_stream_6653_);
                    lean_dec_ref(v_step_6652_);
                    v_a_6657_ = lean_ctor_get(v_x_6655_, 0);
                    v_isSharedCheck_6665_ = (!lean_is_exclusive(v_x_6655_)) as u8;
                    if v_isSharedCheck_6665_ == 0 {
                        v___x_6659_ = v_x_6655_;
                        v_isShared_6660_ = v_isSharedCheck_6665_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6657_);
                        lean_dec(v_x_6655_);
                        v___x_6659_ = lean_box(0);
                        v_isShared_6660_ = v_isSharedCheck_6665_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6666_ = lean_ctor_get(v_x_6655_, 0);
                    v_isSharedCheck_6683_ = (!lean_is_exclusive(v_x_6655_)) as u8;
                    if v_isSharedCheck_6683_ == 0 {
                        v___x_6668_ = v_x_6655_;
                        v_isShared_6669_ = v_isSharedCheck_6683_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6666_);
                        lean_dec(v_x_6655_);
                        v___x_6668_ = lean_box(0);
                        v_isShared_6669_ = v_isSharedCheck_6683_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6660_ == 0 {
                    v___x_6662_ = v___x_6659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6664_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6664_, 0, v_a_6657_);
                    v___x_6662_ = v_reuseFailAlloc_6664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6663_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6663_, 0, v___x_6662_);
                return v___x_6663_;
            }
            3 => {
                if lean_obj_tag(v_a_6666_) == 0 {
                    lean_dec_ref(v_stream_6653_);
                    lean_dec_ref(v_step_6652_);
                    v_a_6670_ = lean_ctor_get(v_a_6666_, 0);
                    v_isSharedCheck_6680_ = (!lean_is_exclusive(v_a_6666_)) as u8;
                    if v_isSharedCheck_6680_ == 0 {
                        v___x_6672_ = v_a_6666_;
                        v_isShared_6673_ = v_isSharedCheck_6680_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6670_);
                        lean_dec(v_a_6666_);
                        v___x_6672_ = lean_box(0);
                        v_isShared_6673_ = v_isSharedCheck_6680_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6668_);
                    v_a_6681_ = lean_ctor_get(v_a_6666_, 0);
                    lean_inc(v_a_6681_);
                    lean_dec_ref_known(v_a_6666_, 1);
                    v___x_6682_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(v_step_6652_, v_stream_6653_, v_a_6681_, v_a_6654_);
                    return v___x_6682_;
                }
            }
            4 => {
                if v_isShared_6669_ == 0 {
                    lean_ctor_set(v___x_6668_, 0, v_a_6670_);
                    v___x_6675_ = v___x_6668_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_a_6670_);
                    v___x_6675_ = v_reuseFailAlloc_6679_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6673_ == 0 {
                    lean_ctor_set(v___x_6672_, 0, v___x_6675_);
                    v___x_6677_ = v___x_6672_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6678_, 0, v___x_6675_);
                    v___x_6677_ = v_reuseFailAlloc_6678_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg___boxed(
    mut v_step_6684_: *mut LeanObject,
    mut v_stream_6685_: *mut LeanObject,
    mut v_acc_6686_: *mut LeanObject,
    mut v_a_6687_: *mut LeanObject,
    mut v_a_6688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6689_: *mut LeanObject = core::ptr::null_mut();
    v_res_6689_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(
            v_step_6684_,
            v_stream_6685_,
            v_acc_6686_,
            v_a_6687_,
        );
    lean_dec_ref(v_a_6687_);
    return v_res_6689_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(
    mut v_00_u03b2_6690_: *mut LeanObject,
    mut v_step_6691_: *mut LeanObject,
    mut v_stream_6692_: *mut LeanObject,
    mut v_acc_6693_: *mut LeanObject,
    mut v_a_6694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    v___x_6696_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(
            v_step_6691_,
            v_stream_6692_,
            v_acc_6693_,
            v_a_6694_,
        );
    return v___x_6696_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___boxed(
    mut v_00_u03b2_6697_: *mut LeanObject,
    mut v_step_6698_: *mut LeanObject,
    mut v_stream_6699_: *mut LeanObject,
    mut v_acc_6700_: *mut LeanObject,
    mut v_a_6701_: *mut LeanObject,
    mut v_a_6702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6703_: *mut LeanObject = core::ptr::null_mut();
    v_res_6703_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop(
        v_00_u03b2_6697_,
        v_step_6698_,
        v_stream_6699_,
        v_acc_6700_,
        v_a_6701_,
    );
    lean_dec_ref(v_a_6701_);
    return v_res_6703_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn_x27___redArg(
    mut v_stream_6704_: *mut LeanObject,
    mut v_acc_6705_: *mut LeanObject,
    mut v_step_6706_: *mut LeanObject,
    mut v_a_6707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6709_: *mut LeanObject = core::ptr::null_mut();
    v___x_6709_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(
            v_step_6706_,
            v_stream_6704_,
            v_acc_6705_,
            v_a_6707_,
        );
    return v___x_6709_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn_x27___redArg___boxed(
    mut v_stream_6710_: *mut LeanObject,
    mut v_acc_6711_: *mut LeanObject,
    mut v_step_6712_: *mut LeanObject,
    mut v_a_6713_: *mut LeanObject,
    mut v_a_6714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6715_: *mut LeanObject = core::ptr::null_mut();
    v_res_6715_ = l_Std_Http_Body_Stream_forIn_x27___redArg(
        v_stream_6710_,
        v_acc_6711_,
        v_step_6712_,
        v_a_6713_,
    );
    lean_dec_ref(v_a_6713_);
    return v_res_6715_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn_x27(
    mut v_00_u03b2_6716_: *mut LeanObject,
    mut v_stream_6717_: *mut LeanObject,
    mut v_acc_6718_: *mut LeanObject,
    mut v_step_6719_: *mut LeanObject,
    mut v_a_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    v___x_6722_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_forIn_x27_loop___redArg(
            v_step_6719_,
            v_stream_6717_,
            v_acc_6718_,
            v_a_6720_,
        );
    return v___x_6722_;
}
pub unsafe fn l_Std_Http_Body_Stream_forIn_x27___boxed(
    mut v_00_u03b2_6723_: *mut LeanObject,
    mut v_stream_6724_: *mut LeanObject,
    mut v_acc_6725_: *mut LeanObject,
    mut v_step_6726_: *mut LeanObject,
    mut v_a_6727_: *mut LeanObject,
    mut v_a_6728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6729_: *mut LeanObject = core::ptr::null_mut();
    v_res_6729_ = l_Std_Http_Body_Stream_forIn_x27(
        v_00_u03b2_6723_,
        v_stream_6724_,
        v_acc_6725_,
        v_step_6726_,
        v_a_6727_,
    );
    lean_dec_ref(v_a_6727_);
    return v_res_6729_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(
    mut v_x_6732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    v___x_6734_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__1;
    return v___x_6734_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0___boxed(
    mut v_x_6735_: *mut LeanObject,
    mut v___y_6736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6737_: *mut LeanObject = core::ptr::null_mut();
    v_res_6737_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__0(v_x_6735_);
    return v_res_6737_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(
    mut v___y_6738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    v___x_6740_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6740_, 0, v___y_6738_);
    v___x_6741_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6741_, 0, v___x_6740_);
    return v___x_6741_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1___boxed(
    mut v___y_6742_: *mut LeanObject,
    mut v___y_6743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6744_: *mut LeanObject = core::ptr::null_mut();
    v_res_6744_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__1(v___y_6742_);
    return v_res_6744_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(
    mut v_x_6745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6750_: u8 = 0;
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6755_: u8 = 0;
    let mut v_a_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6759_: u8 = 0;
    let mut v_token_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6745_) == 0 {
                    v_a_6747_ = lean_ctor_get(v_x_6745_, 0);
                    v_isSharedCheck_6755_ = (!lean_is_exclusive(v_x_6745_)) as u8;
                    if v_isSharedCheck_6755_ == 0 {
                        v___x_6749_ = v_x_6745_;
                        v_isShared_6750_ = v_isSharedCheck_6755_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6747_);
                        lean_dec(v_x_6745_);
                        v___x_6749_ = lean_box(0);
                        v_isShared_6750_ = v_isSharedCheck_6755_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6756_ = lean_ctor_get(v_x_6745_, 0);
                    v_isSharedCheck_6766_ = (!lean_is_exclusive(v_x_6745_)) as u8;
                    if v_isSharedCheck_6766_ == 0 {
                        v___x_6758_ = v_x_6745_;
                        v_isShared_6759_ = v_isSharedCheck_6766_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6756_);
                        lean_dec(v_x_6745_);
                        v___x_6758_ = lean_box(0);
                        v_isShared_6759_ = v_isSharedCheck_6766_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6750_ == 0 {
                    v___x_6752_ = v___x_6749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6754_, 0, v_a_6747_);
                    v___x_6752_ = v_reuseFailAlloc_6754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6753_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6753_, 0, v___x_6752_);
                return v___x_6753_;
            }
            3 => {
                v_token_6760_ = lean_ctor_get(v_a_6756_, 1);
                lean_inc_ref(v_token_6760_);
                lean_dec(v_a_6756_);
                v___x_6761_ = l_Std_CancellationToken_selector(v_token_6760_);
                if v_isShared_6759_ == 0 {
                    lean_ctor_set(v___x_6758_, 0, v___x_6761_);
                    v___x_6763_ = v___x_6758_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6765_, 0, v___x_6761_);
                    v___x_6763_ = v_reuseFailAlloc_6765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6764_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6764_, 0, v___x_6763_);
                return v___x_6764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2___boxed(
    mut v_x_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6769_: *mut LeanObject = core::ptr::null_mut();
    v_res_6769_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__2(v_x_6767_);
    return v_res_6769_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(
    mut v_stream_6770_: *mut LeanObject,
    mut v___f_6771_: *mut LeanObject,
    mut v___f_6772_: *mut LeanObject,
    mut v_x_6773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6778_: u8 = 0;
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6783_: u8 = 0;
    let mut v_a_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6773_) == 0 {
                    lean_dec_ref(v___f_6772_);
                    lean_dec_ref(v___f_6771_);
                    lean_dec_ref(v_stream_6770_);
                    v_a_6775_ = lean_ctor_get(v_x_6773_, 0);
                    v_isSharedCheck_6783_ = (!lean_is_exclusive(v_x_6773_)) as u8;
                    if v_isSharedCheck_6783_ == 0 {
                        v___x_6777_ = v_x_6773_;
                        v_isShared_6778_ = v_isSharedCheck_6783_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6775_);
                        lean_dec(v_x_6773_);
                        v___x_6777_ = lean_box(0);
                        v_isShared_6778_ = v_isSharedCheck_6783_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6784_ = lean_ctor_get(v_x_6773_, 0);
                    lean_inc(v_a_6784_);
                    lean_dec_ref_known(v_x_6773_, 1);
                    v___x_6785_ = l_Std_Http_Body_Stream_recvSelector(v_stream_6770_);
                    v___x_6786_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6786_, 0, v___x_6785_);
                    lean_ctor_set(v___x_6786_, 1, v___f_6771_);
                    v___x_6787_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6787_, 0, v_a_6784_);
                    lean_ctor_set(v___x_6787_, 1, v___f_6772_);
                    v___x_6788_ = lean_unsigned_to_nat(2);
                    v___x_6789_ = lean_mk_empty_array_with_capacity(v___x_6788_);
                    v___x_6790_ = lean_array_push(v___x_6789_, v___x_6786_);
                    v___x_6791_ = lean_array_push(v___x_6790_, v___x_6787_);
                    v___x_6792_ = l_Std_Async_Selectable_one___redArg(v___x_6791_);
                    return v___x_6792_;
                }
            }
            1 => {
                if v_isShared_6778_ == 0 {
                    v___x_6780_ = v___x_6777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6782_, 0, v_a_6775_);
                    v___x_6780_ = v_reuseFailAlloc_6782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6781_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6781_, 0, v___x_6780_);
                return v___x_6781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed(
    mut v_stream_6793_: *mut LeanObject,
    mut v___f_6794_: *mut LeanObject,
    mut v___f_6795_: *mut LeanObject,
    mut v_x_6796_: *mut LeanObject,
    mut v___y_6797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6798_: *mut LeanObject = core::ptr::null_mut();
    v_res_6798_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3(
        v_stream_6793_,
        v___f_6794_,
        v___f_6795_,
        v_x_6796_,
    );
    return v_res_6798_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(
    mut v___f_6799_: *mut LeanObject,
    mut v___f_6800_: *mut LeanObject,
    mut v___f_6801_: *mut LeanObject,
    mut v_stream_6802_: *mut LeanObject,
    mut v___y_6803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: u8 = 0;
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_6803_);
    v___x_6805_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6805_, 0, v___y_6803_);
    v___x_6806_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6806_, 0, v___x_6805_);
    v___x_6807_ = lean_unsigned_to_nat(0);
    v___x_6808_ = 0;
    v___x_6809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6807_,
        v___x_6808_,
        v___x_6806_,
        v___f_6799_,
    );
    v___f_6810_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_6810_, 0, v_stream_6802_);
    lean_closure_set(v___f_6810_, 1, v___f_6800_);
    lean_closure_set(v___f_6810_, 2, v___f_6801_);
    v___x_6811_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6807_,
        v___x_6808_,
        v___x_6809_,
        v___f_6810_,
    );
    return v___x_6811_;
}
pub unsafe fn l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4___boxed(
    mut v___f_6812_: *mut LeanObject,
    mut v___f_6813_: *mut LeanObject,
    mut v___f_6814_: *mut LeanObject,
    mut v_stream_6815_: *mut LeanObject,
    mut v___y_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6818_: *mut LeanObject = core::ptr::null_mut();
    v_res_6818_ = l_Std_Http_Body_Stream_instNextChunkContextAsync___lam__4(
        v___f_6812_,
        v___f_6813_,
        v___f_6814_,
        v_stream_6815_,
        v___y_6816_,
    );
    lean_dec_ref(v___y_6816_);
    return v_res_6818_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1(
    mut v_toPure_6829_: *mut LeanObject,
    mut v_result_6830_: *mut LeanObject,
    mut v_maximumSize_6831_: *mut LeanObject,
    mut v_inst_6832_: *mut LeanObject,
    mut v_inst_6833_: *mut LeanObject,
    mut v_inst_6834_: *mut LeanObject,
    mut v_stream_6835_: *mut LeanObject,
    mut v_toBind_6836_: *mut LeanObject,
    mut v_____do__lift_6837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6842_: u8 = 0;
    let mut v_data_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: u8 = 0;
    let mut v_result_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: u64 = 0;
    let mut v___x_6852_: u64 = 0;
    let mut v___x_6853_: u8 = 0;
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throw_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: u64 = 0;
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_6837_) == 0 {
                    lean_dec(v_toBind_6836_);
                    lean_dec_ref(v_stream_6835_);
                    lean_dec(v_inst_6834_);
                    lean_dec_ref(v_inst_6833_);
                    lean_dec_ref(v_inst_6832_);
                    lean_dec(v_maximumSize_6831_);
                    v___x_6838_ = lean_apply_2(v_toPure_6829_, lean_box(0), v_result_6830_);
                    return v___x_6838_;
                } else {
                    lean_dec(v_toPure_6829_);
                    v_val_6839_ = lean_ctor_get(v_____do__lift_6837_, 0);
                    v_isSharedCheck_6870_ = (!lean_is_exclusive(v_____do__lift_6837_)) as u8;
                    if v_isSharedCheck_6870_ == 0 {
                        v___x_6841_ = v_____do__lift_6837_;
                        v_isShared_6842_ = v_isSharedCheck_6870_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6839_);
                        lean_dec(v_____do__lift_6837_);
                        v___x_6841_ = lean_box(0);
                        v_isShared_6842_ = v_isSharedCheck_6870_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_data_6843_ = lean_ctor_get(v_val_6839_, 0);
                lean_inc_ref(v_data_6843_);
                lean_dec(v_val_6839_);
                v___x_6844_ = lean_unsigned_to_nat(0);
                v___x_6845_ = lean_byte_array_size(v_result_6830_);
                v___x_6846_ = lean_byte_array_size(v_data_6843_);
                v___x_6847_ = 0;
                v_result_6848_ = lean_byte_array_copy_slice(
                    v_data_6843_,
                    v___x_6844_,
                    v_result_6830_,
                    v___x_6845_,
                    v___x_6846_,
                    v___x_6847_,
                );
                lean_dec_ref(v_data_6843_);
                if lean_obj_tag(v_maximumSize_6831_) == 1 {
                    v_val_6849_ = lean_ctor_get(v_maximumSize_6831_, 0);
                    v___x_6850_ = lean_byte_array_size(v_result_6848_);
                    v___x_6851_ = lean_uint64_of_nat(v___x_6850_);
                    v___x_6852_ = lean_unbox_uint64(v_val_6849_);
                    v___x_6853_ = lean_uint64_dec_lt(v___x_6852_, v___x_6851_);
                    if v___x_6853_ == 0 {
                        lean_del_object(v___x_6841_);
                        lean_dec(v_toBind_6836_);
                        v___x_6854_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_6832_, v_inst_6833_, v_inst_6834_, v_stream_6835_, v_maximumSize_6831_, v_result_6848_);
                        return v___x_6854_;
                    } else {
                        lean_inc(v_val_6849_);
                        v_throw_6855_ = lean_ctor_get(v_inst_6833_, 0);
                        lean_inc(v_throw_6855_);
                        v___f_6856_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0 as *mut core::ffi::c_void, 7, 6);
                        lean_closure_set(v___f_6856_, 0, v_inst_6832_);
                        lean_closure_set(v___f_6856_, 1, v_inst_6833_);
                        lean_closure_set(v___f_6856_, 2, v_inst_6834_);
                        lean_closure_set(v___f_6856_, 3, v_stream_6835_);
                        lean_closure_set(v___f_6856_, 4, v_maximumSize_6831_);
                        lean_closure_set(v___f_6856_, 5, v_result_6848_);
                        v___x_6857_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__0;
                        v___x_6858_ = lean_unbox_uint64(v_val_6849_);
                        lean_dec(v_val_6849_);
                        v___x_6859_ = lean_uint64_to_nat(v___x_6858_);
                        v___x_6860_ = l_Nat_reprFast(v___x_6859_);
                        v___x_6861_ = lean_string_append(v___x_6857_, v___x_6860_);
                        lean_dec_ref(v___x_6860_);
                        v___x_6862_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1___closed__1;
                        v___x_6863_ = lean_string_append(v___x_6861_, v___x_6862_);
                        if v_isShared_6842_ == 0 {
                            lean_ctor_set_tag(v___x_6841_, 18);
                            lean_ctor_set(v___x_6841_, 0, v___x_6863_);
                            v___x_6865_ = v___x_6841_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6868_ = lean_alloc_ctor(18, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6868_, 0, v___x_6863_);
                            v___x_6865_ = v_reuseFailAlloc_6868_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6841_);
                    lean_dec(v_toBind_6836_);
                    v___x_6869_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(v_inst_6832_, v_inst_6833_, v_inst_6834_, v_stream_6835_, v_maximumSize_6831_, v_result_6848_);
                    return v___x_6869_;
                }
            }
            2 => {
                v___x_6866_ = lean_apply_2(v_throw_6855_, lean_box(0), v___x_6865_);
                v___x_6867_ = lean_apply_4(
                    v_toBind_6836_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6866_,
                    v___f_6856_,
                );
                return v___x_6867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(
    mut v_inst_6871_: *mut LeanObject,
    mut v_inst_6872_: *mut LeanObject,
    mut v_inst_6873_: *mut LeanObject,
    mut v_stream_6874_: *mut LeanObject,
    mut v_maximumSize_6875_: *mut LeanObject,
    mut v_result_6876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6877_ = lean_ctor_get(v_inst_6871_, 0);
    v_toBind_6878_ = lean_ctor_get(v_inst_6871_, 1);
    lean_inc_n(v_toBind_6878_, 2);
    v_toPure_6879_ = lean_ctor_get(v_toApplicative_6877_, 1);
    lean_inc(v_toPure_6879_);
    lean_inc(v_inst_6873_);
    lean_inc_ref(v_stream_6874_);
    v___x_6880_ = lean_apply_1(v_inst_6873_, v_stream_6874_);
    v___f_6881_ = lean_alloc_closure(
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__1
            as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_6881_, 0, v_toPure_6879_);
    lean_closure_set(v___f_6881_, 1, v_result_6876_);
    lean_closure_set(v___f_6881_, 2, v_maximumSize_6875_);
    lean_closure_set(v___f_6881_, 3, v_inst_6871_);
    lean_closure_set(v___f_6881_, 4, v_inst_6872_);
    lean_closure_set(v___f_6881_, 5, v_inst_6873_);
    lean_closure_set(v___f_6881_, 6, v_stream_6874_);
    lean_closure_set(v___f_6881_, 7, v_toBind_6878_);
    v___x_6882_ = lean_apply_4(
        v_toBind_6878_,
        lean_box(0),
        lean_box(0),
        v___x_6880_,
        v___f_6881_,
    );
    return v___x_6882_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg___lam__0(
    mut v_inst_6883_: *mut LeanObject,
    mut v_inst_6884_: *mut LeanObject,
    mut v_inst_6885_: *mut LeanObject,
    mut v_stream_6886_: *mut LeanObject,
    mut v_maximumSize_6887_: *mut LeanObject,
    mut v_result_6888_: *mut LeanObject,
    mut v_____r_6889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    v___x_6890_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(
            v_inst_6883_,
            v_inst_6884_,
            v_inst_6885_,
            v_stream_6886_,
            v_maximumSize_6887_,
            v_result_6888_,
        );
    return v___x_6890_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop(
    mut v_m_6891_: *mut LeanObject,
    mut v_inst_6892_: *mut LeanObject,
    mut v_inst_6893_: *mut LeanObject,
    mut v_inst_6894_: *mut LeanObject,
    mut v_stream_6895_: *mut LeanObject,
    mut v_maximumSize_6896_: *mut LeanObject,
    mut v_result_6897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    v___x_6898_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(
            v_inst_6892_,
            v_inst_6893_,
            v_inst_6894_,
            v_stream_6895_,
            v_maximumSize_6896_,
            v_result_6897_,
        );
    return v___x_6898_;
}
pub unsafe fn l_Std_Http_Body_Stream_readAll___redArg___lam__0(
    mut v_inst_6899_: *mut LeanObject,
    mut v_inst_6900_: *mut LeanObject,
    mut v_toPure_6901_: *mut LeanObject,
    mut v_result_6902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6907_: u8 = 0;
    let mut v_throw_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6913_: u8 = 0;
    let mut v_a_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6903_ = lean_apply_1(v_inst_6899_, v_result_6902_);
                if lean_obj_tag(v___x_6903_) == 0 {
                    lean_dec(v_toPure_6901_);
                    v_a_6904_ = lean_ctor_get(v___x_6903_, 0);
                    v_isSharedCheck_6913_ = (!lean_is_exclusive(v___x_6903_)) as u8;
                    if v_isSharedCheck_6913_ == 0 {
                        v___x_6906_ = v___x_6903_;
                        v_isShared_6907_ = v_isSharedCheck_6913_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6904_);
                        lean_dec(v___x_6903_);
                        v___x_6906_ = lean_box(0);
                        v_isShared_6907_ = v_isSharedCheck_6913_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_6900_);
                    v_a_6914_ = lean_ctor_get(v___x_6903_, 0);
                    lean_inc(v_a_6914_);
                    lean_dec_ref_known(v___x_6903_, 1);
                    v___x_6915_ = lean_apply_2(v_toPure_6901_, lean_box(0), v_a_6914_);
                    return v___x_6915_;
                }
            }
            1 => {
                v_throw_6908_ = lean_ctor_get(v_inst_6900_, 0);
                lean_inc(v_throw_6908_);
                lean_dec_ref(v_inst_6900_);
                if v_isShared_6907_ == 0 {
                    lean_ctor_set_tag(v___x_6906_, 18);
                    v___x_6910_ = v___x_6906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6912_ = lean_alloc_ctor(18, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6912_, 0, v_a_6904_);
                    v___x_6910_ = v_reuseFailAlloc_6912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6911_ = lean_apply_2(v_throw_6908_, lean_box(0), v___x_6910_);
                return v___x_6911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_readAll___redArg(
    mut v_inst_6916_: *mut LeanObject,
    mut v_inst_6917_: *mut LeanObject,
    mut v_inst_6918_: *mut LeanObject,
    mut v_inst_6919_: *mut LeanObject,
    mut v_stream_6920_: *mut LeanObject,
    mut v_maximumSize_6921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6922_ = lean_ctor_get(v_inst_6917_, 0);
    v_toBind_6923_ = lean_ctor_get(v_inst_6917_, 1);
    lean_inc(v_toBind_6923_);
    v_toPure_6924_ = lean_ctor_get(v_toApplicative_6922_, 1);
    lean_inc(v_toPure_6924_);
    v___x_6925_ = l_ByteArray_empty;
    lean_inc_ref(v_inst_6918_);
    v___x_6926_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_readAll_loop___redArg(
            v_inst_6917_,
            v_inst_6918_,
            v_inst_6919_,
            v_stream_6920_,
            v_maximumSize_6921_,
            v___x_6925_,
        );
    v___f_6927_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_readAll___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6927_, 0, v_inst_6916_);
    lean_closure_set(v___f_6927_, 1, v_inst_6918_);
    lean_closure_set(v___f_6927_, 2, v_toPure_6924_);
    v___x_6928_ = lean_apply_4(
        v_toBind_6923_,
        lean_box(0),
        lean_box(0),
        v___x_6926_,
        v___f_6927_,
    );
    return v___x_6928_;
}
pub unsafe fn l_Std_Http_Body_Stream_readAll(
    mut v_00_u03b1_6929_: *mut LeanObject,
    mut v_m_6930_: *mut LeanObject,
    mut v_inst_6931_: *mut LeanObject,
    mut v_inst_6932_: *mut LeanObject,
    mut v_inst_6933_: *mut LeanObject,
    mut v_inst_6934_: *mut LeanObject,
    mut v_stream_6935_: *mut LeanObject,
    mut v_maximumSize_6936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    v___x_6937_ = l_Std_Http_Body_Stream_readAll___redArg(
        v_inst_6931_,
        v_inst_6932_,
        v_inst_6933_,
        v_inst_6934_,
        v_stream_6935_,
        v_maximumSize_6936_,
    );
    return v___x_6937_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(
    mut v_incomplete_6943_: u8,
    mut v_chunk_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6952_: u8 = 0;
    let mut v_knownSize_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6957_: u8 = 0;
    let mut v___y_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6980_: u8 = 0;
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: u8 = 0;
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6993_: u8 = 0;
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6947_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__0(v___y_6945_);
                v___x_6948_ = lean_st_ref_get(v___y_6945_);
                v_pendingProducer_6949_ = lean_ctor_get(v___x_6948_, 0);
                v_pendingConsumer_6950_ = lean_ctor_get(v___x_6948_, 1);
                v_interestWaiter_6951_ = lean_ctor_get(v___x_6948_, 2);
                v_closed_6952_ = lean_ctor_get_uint8(
                    v___x_6948_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_knownSize_6953_ = lean_ctor_get(v___x_6948_, 3);
                v_pendingIncompleteChunk_6954_ = lean_ctor_get(v___x_6948_, 4);
                v_isSharedCheck_6995_ = (!lean_is_exclusive(v___x_6948_)) as u8;
                if v_isSharedCheck_6995_ == 0 {
                    v___x_6956_ = v___x_6948_;
                    v_isShared_6957_ = v_isSharedCheck_6995_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pendingIncompleteChunk_6954_);
                    lean_inc(v_knownSize_6953_);
                    lean_inc(v_interestWaiter_6951_);
                    lean_inc(v_pendingConsumer_6950_);
                    lean_inc(v_pendingProducer_6949_);
                    lean_dec(v___x_6948_);
                    v___x_6956_ = lean_box(0);
                    v_isShared_6957_ = v_isSharedCheck_6995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_closed_6952_ == 0 {
                    if lean_obj_tag(v_pendingIncompleteChunk_6954_) == 0 {
                        v___y_6959_ = v_chunk_6944_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6973_ = lean_ctor_get(v_pendingIncompleteChunk_6954_, 0);
                        lean_inc(v_val_6973_);
                        lean_dec_ref_known(v_pendingIncompleteChunk_6954_, 1);
                        v_data_6974_ = lean_ctor_get(v_val_6973_, 0);
                        lean_inc_ref(v_data_6974_);
                        v_extensions_6975_ = lean_ctor_get(v_val_6973_, 1);
                        lean_inc_ref(v_extensions_6975_);
                        lean_dec(v_val_6973_);
                        v_data_6976_ = lean_ctor_get(v_chunk_6944_, 0);
                        v_extensions_6977_ = lean_ctor_get(v_chunk_6944_, 1);
                        v_isSharedCheck_6993_ = (!lean_is_exclusive(v_chunk_6944_)) as u8;
                        if v_isSharedCheck_6993_ == 0 {
                            v___x_6979_ = v_chunk_6944_;
                            v_isShared_6980_ = v_isSharedCheck_6993_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_extensions_6977_);
                            lean_inc(v_data_6976_);
                            lean_dec(v_chunk_6944_);
                            v___x_6979_ = lean_box(0);
                            v_isShared_6980_ = v_isSharedCheck_6993_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6956_);
                    lean_dec(v_pendingIncompleteChunk_6954_);
                    lean_dec(v_knownSize_6953_);
                    lean_dec(v_interestWaiter_6951_);
                    lean_dec(v_pendingConsumer_6950_);
                    lean_dec(v_pendingProducer_6949_);
                    lean_dec_ref(v_chunk_6944_);
                    v___x_6994_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___closed__2;
                    return v___x_6994_;
                }
            }
            2 => {
                if v_incomplete_6943_ == 0 {
                    v___x_6960_ = lean_box(0);
                    if v_isShared_6957_ == 0 {
                        lean_ctor_set(v___x_6956_, 4, v___x_6960_);
                        v___x_6962_ = v___x_6956_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6966_ = lean_alloc_ctor(0, 5, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6966_, 0, v_pendingProducer_6949_);
                        lean_ctor_set(v_reuseFailAlloc_6966_, 1, v_pendingConsumer_6950_);
                        lean_ctor_set(v_reuseFailAlloc_6966_, 2, v_interestWaiter_6951_);
                        lean_ctor_set(v_reuseFailAlloc_6966_, 3, v_knownSize_6953_);
                        lean_ctor_set(v_reuseFailAlloc_6966_, 4, v___x_6960_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_6966_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                            v_closed_6952_,
                        );
                        v___x_6962_ = v_reuseFailAlloc_6966_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6967_, 0, v___y_6959_);
                    if v_isShared_6957_ == 0 {
                        lean_ctor_set(v___x_6956_, 4, v___x_6967_);
                        v___x_6969_ = v___x_6956_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6972_ = lean_alloc_ctor(0, 5, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6972_, 0, v_pendingProducer_6949_);
                        lean_ctor_set(v_reuseFailAlloc_6972_, 1, v_pendingConsumer_6950_);
                        lean_ctor_set(v_reuseFailAlloc_6972_, 2, v_interestWaiter_6951_);
                        lean_ctor_set(v_reuseFailAlloc_6972_, 3, v_knownSize_6953_);
                        lean_ctor_set(v_reuseFailAlloc_6972_, 4, v___x_6967_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_6972_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                            v_closed_6952_,
                        );
                        v___x_6969_ = v_reuseFailAlloc_6972_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6963_ = lean_st_ref_set(v___y_6945_, v___x_6962_);
                v___x_6964_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6964_, 0, v___y_6959_);
                v___x_6965_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6965_, 0, v___x_6964_);
                return v___x_6965_;
            }
            4 => {
                v___x_6970_ = lean_st_ref_set(v___y_6945_, v___x_6969_);
                v___x_6971_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__2___closed__0;
                return v___x_6971_;
            }
            5 => {
                v___x_6981_ = lean_unsigned_to_nat(0);
                v___x_6982_ = lean_byte_array_size(v_data_6974_);
                v___x_6983_ = lean_byte_array_size(v_data_6976_);
                v___x_6984_ = lean_byte_array_copy_slice(
                    v_data_6976_,
                    v___x_6981_,
                    v_data_6974_,
                    v___x_6982_,
                    v___x_6983_,
                    v_closed_6952_,
                );
                lean_dec_ref(v_data_6976_);
                v___x_6985_ = lean_array_get_size(v_extensions_6975_);
                v___x_6986_ = lean_nat_dec_eq(v___x_6985_, v___x_6981_);
                if v___x_6986_ == 0 {
                    lean_dec_ref(v_extensions_6977_);
                    if v_isShared_6980_ == 0 {
                        lean_ctor_set(v___x_6979_, 1, v_extensions_6975_);
                        lean_ctor_set(v___x_6979_, 0, v___x_6984_);
                        v___x_6988_ = v___x_6979_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6989_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6989_, 0, v___x_6984_);
                        lean_ctor_set(v_reuseFailAlloc_6989_, 1, v_extensions_6975_);
                        v___x_6988_ = v_reuseFailAlloc_6989_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_extensions_6975_);
                    if v_isShared_6980_ == 0 {
                        lean_ctor_set(v___x_6979_, 0, v___x_6984_);
                        v___x_6991_ = v___x_6979_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6992_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6992_, 0, v___x_6984_);
                        lean_ctor_set(v_reuseFailAlloc_6992_, 1, v_extensions_6977_);
                        v___x_6991_ = v_reuseFailAlloc_6992_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___y_6959_ = v___x_6988_;
                state = 2;
                continue;
            }
            7 => {
                v___y_6959_ = v___x_6991_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed(
    mut v_incomplete_6996_: *mut LeanObject,
    mut v_chunk_6997_: *mut LeanObject,
    mut v___y_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_incomplete_boxed_7000_: u8 = 0;
    let mut v_res_7001_: *mut LeanObject = core::ptr::null_mut();
    v_incomplete_boxed_7000_ = (lean_unbox(v_incomplete_6996_) as u8);
    v_res_7001_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0(
            v_incomplete_boxed_7000_,
            v_chunk_6997_,
            v___y_6998_,
        );
    lean_dec(v___y_6998_);
    return v_res_7001_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(
    mut v_stream_7002_: *mut LeanObject,
    mut v_chunk_7003_: *mut LeanObject,
    mut v_incomplete_7004_: u8,
) -> *mut LeanObject {
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    v___x_7006_ = lean_box((v_incomplete_7004_) as usize);
    v___f_7007_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_7007_, 0, v___x_7006_);
    lean_closure_set(v___f_7007_, 1, v_chunk_7003_);
    v___x_7008_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_recv_x27_spec__3___redArg(v_stream_7002_, v___f_7007_);
    return v___x_7008_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend___boxed(
    mut v_stream_7009_: *mut LeanObject,
    mut v_chunk_7010_: *mut LeanObject,
    mut v_incomplete_7011_: *mut LeanObject,
    mut v_a_7012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_incomplete_boxed_7013_: u8 = 0;
    let mut v_res_7014_: *mut LeanObject = core::ptr::null_mut();
    v_incomplete_boxed_7013_ = (lean_unbox(v_incomplete_7011_) as u8);
    v_res_7014_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(
        v_stream_7009_,
        v_chunk_7010_,
        v_incomplete_boxed_7013_,
    );
    return v_res_7014_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(
    mut v_x_7021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7026_: u8 = 0;
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7031_: u8 = 0;
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7021_) == 0 {
                    v_a_7023_ = lean_ctor_get(v_x_7021_, 0);
                    v_isSharedCheck_7031_ = (!lean_is_exclusive(v_x_7021_)) as u8;
                    if v_isSharedCheck_7031_ == 0 {
                        v___x_7025_ = v_x_7021_;
                        v_isShared_7026_ = v_isSharedCheck_7031_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7023_);
                        lean_dec(v_x_7021_);
                        v___x_7025_ = lean_box(0);
                        v_isShared_7026_ = v_isSharedCheck_7031_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_7021_, 1);
                    v___x_7032_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___closed__2;
                    return v___x_7032_;
                }
            }
            1 => {
                if v_isShared_7026_ == 0 {
                    v___x_7028_ = v___x_7025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7030_, 0, v_a_7023_);
                    v___x_7028_ = v_reuseFailAlloc_7030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7029_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7029_, 0, v___x_7028_);
                return v___x_7029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0___boxed(
    mut v_x_7033_: *mut LeanObject,
    mut v___y_7034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7035_: *mut LeanObject = core::ptr::null_mut();
    v_res_7035_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__0(v_x_7033_);
    return v_res_7035_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(
    mut v_00___7036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7038_: *mut LeanObject = core::ptr::null_mut();
    v___x_7038_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
    return v___x_7038_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1___boxed(
    mut v_00___7039_: *mut LeanObject,
    mut v___y_7040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7041_: *mut LeanObject = core::ptr::null_mut();
    v_res_7041_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__1(
        v_00___7039_,
    );
    return v_res_7041_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(
    mut v___f_7046_: *mut LeanObject,
    mut v_x_7047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7054_: u8 = 0;
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7059_: u8 = 0;
    let mut v_a_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: u8 = 0;
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7047_) == 0 {
                    lean_dec_ref(v___f_7046_);
                    v_a_7051_ = lean_ctor_get(v_x_7047_, 0);
                    v_isSharedCheck_7059_ = (!lean_is_exclusive(v_x_7047_)) as u8;
                    if v_isSharedCheck_7059_ == 0 {
                        v___x_7053_ = v_x_7047_;
                        v_isShared_7054_ = v_isSharedCheck_7059_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7051_);
                        lean_dec(v_x_7047_);
                        v___x_7053_ = lean_box(0);
                        v_isShared_7054_ = v_isSharedCheck_7059_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7060_ = lean_ctor_get(v_x_7047_, 0);
                    lean_inc(v_a_7060_);
                    lean_dec_ref_known(v_x_7047_, 1);
                    if lean_obj_tag(v_a_7060_) == 1 {
                        v_val_7061_ = lean_ctor_get(v_a_7060_, 0);
                        lean_inc(v_val_7061_);
                        lean_dec_ref_known(v_a_7060_, 1);
                        v___x_7062_ = (lean_unbox(v_val_7061_) as u8);
                        lean_dec(v_val_7061_);
                        if v___x_7062_ == 1 {
                            v___x_7063_ = lean_box(0);
                            v___x_7064_ = lean_apply_2(v___f_7046_, v___x_7063_, lean_box(0));
                            return v___x_7064_;
                        } else {
                            lean_dec_ref(v___f_7046_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7060_);
                        lean_dec_ref(v___f_7046_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7050_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___closed__1;
                return v___x_7050_;
            }
            2 => {
                if v_isShared_7054_ == 0 {
                    v___x_7056_ = v___x_7053_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7058_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_a_7051_);
                    v___x_7056_ = v_reuseFailAlloc_7058_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7057_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7057_, 0, v___x_7056_);
                return v___x_7057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2___boxed(
    mut v___f_7065_: *mut LeanObject,
    mut v_x_7066_: *mut LeanObject,
    mut v___y_7067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7068_: *mut LeanObject = core::ptr::null_mut();
    v_res_7068_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__2(
        v___f_7065_,
        v_x_7066_,
    );
    return v_res_7068_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__3(
    mut v_a_7069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    v___x_7070_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7070_, 0, v_a_7069_);
    return v___x_7070_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(
    mut v___x_7071_: u8,
    mut v_x_7072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7077_: u8 = 0;
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7082_: u8 = 0;
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7085_: u8 = 0;
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7093_: u8 = 0;
    let mut v_unused_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7072_) == 0 {
                    v_a_7074_ = lean_ctor_get(v_x_7072_, 0);
                    v_isSharedCheck_7082_ = (!lean_is_exclusive(v_x_7072_)) as u8;
                    if v_isSharedCheck_7082_ == 0 {
                        v___x_7076_ = v_x_7072_;
                        v_isShared_7077_ = v_isSharedCheck_7082_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7074_);
                        lean_dec(v_x_7072_);
                        v___x_7076_ = lean_box(0);
                        v_isShared_7077_ = v_isSharedCheck_7082_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_7093_ = (!lean_is_exclusive(v_x_7072_)) as u8;
                    if v_isSharedCheck_7093_ == 0 {
                        v_unused_7094_ = lean_ctor_get(v_x_7072_, 0);
                        lean_dec(v_unused_7094_);
                        v___x_7084_ = v_x_7072_;
                        v_isShared_7085_ = v_isSharedCheck_7093_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_7072_);
                        v___x_7084_ = lean_box(0);
                        v_isShared_7085_ = v_isSharedCheck_7093_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7077_ == 0 {
                    v___x_7079_ = v___x_7076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7081_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_a_7074_);
                    v___x_7079_ = v_reuseFailAlloc_7081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7080_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7080_, 0, v___x_7079_);
                return v___x_7080_;
            }
            3 => {
                v___x_7086_ = lean_box((v___x_7071_) as usize);
                v___x_7087_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7087_, 0, v___x_7086_);
                if v_isShared_7085_ == 0 {
                    lean_ctor_set(v___x_7084_, 0, v___x_7087_);
                    v___x_7089_ = v___x_7084_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7092_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7092_, 0, v___x_7087_);
                    v___x_7089_ = v_reuseFailAlloc_7092_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7090_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7090_, 0, v___x_7089_);
                v___x_7091_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7091_, 0, v___x_7090_);
                return v___x_7091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4___boxed(
    mut v___x_7095_: *mut LeanObject,
    mut v_x_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5677__boxed_7098_: u8 = 0;
    let mut v_res_7099_: *mut LeanObject = core::ptr::null_mut();
    v___x_5677__boxed_7098_ = (lean_unbox(v___x_7095_) as u8);
    v_res_7099_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__4(
        v___x_5677__boxed_7098_,
        v_x_7096_,
    );
    return v_res_7099_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(
    mut v_a_7100_: u8,
    mut v_x_7101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7106_: u8 = 0;
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7111_: u8 = 0;
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7114_: u8 = 0;
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7122_: u8 = 0;
    let mut v_unused_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7101_) == 0 {
                    v_a_7103_ = lean_ctor_get(v_x_7101_, 0);
                    v_isSharedCheck_7111_ = (!lean_is_exclusive(v_x_7101_)) as u8;
                    if v_isSharedCheck_7111_ == 0 {
                        v___x_7105_ = v_x_7101_;
                        v_isShared_7106_ = v_isSharedCheck_7111_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7103_);
                        lean_dec(v_x_7101_);
                        v___x_7105_ = lean_box(0);
                        v_isShared_7106_ = v_isSharedCheck_7111_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_7122_ = (!lean_is_exclusive(v_x_7101_)) as u8;
                    if v_isSharedCheck_7122_ == 0 {
                        v_unused_7123_ = lean_ctor_get(v_x_7101_, 0);
                        lean_dec(v_unused_7123_);
                        v___x_7113_ = v_x_7101_;
                        v_isShared_7114_ = v_isSharedCheck_7122_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_7101_);
                        v___x_7113_ = lean_box(0);
                        v_isShared_7114_ = v_isSharedCheck_7122_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7106_ == 0 {
                    v___x_7108_ = v___x_7105_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7110_, 0, v_a_7103_);
                    v___x_7108_ = v_reuseFailAlloc_7110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7109_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7109_, 0, v___x_7108_);
                return v___x_7109_;
            }
            3 => {
                v___x_7115_ = lean_box((v_a_7100_) as usize);
                v___x_7116_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7116_, 0, v___x_7115_);
                if v_isShared_7114_ == 0 {
                    lean_ctor_set(v___x_7113_, 0, v___x_7116_);
                    v___x_7118_ = v___x_7113_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7121_, 0, v___x_7116_);
                    v___x_7118_ = v_reuseFailAlloc_7121_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7119_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7119_, 0, v___x_7118_);
                v___x_7120_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7120_, 0, v___x_7119_);
                return v___x_7120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed(
    mut v_a_7124_: *mut LeanObject,
    mut v_x_7125_: *mut LeanObject,
    mut v___y_7126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5729__boxed_7127_: u8 = 0;
    let mut v_res_7128_: *mut LeanObject = core::ptr::null_mut();
    v_a_5729__boxed_7127_ = (lean_unbox(v_a_7124_) as u8);
    v_res_7128_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5(
        v_a_5729__boxed_7127_,
        v_x_7125_,
    );
    return v_res_7128_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(
    mut v_pendingProducer_7129_: *mut LeanObject,
    mut v_interestWaiter_7130_: *mut LeanObject,
    mut v_closed_7131_: u8,
    mut v_knownSize_7132_: *mut LeanObject,
    mut v_pendingIncompleteChunk_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v_chunk_7135_: *mut LeanObject,
    mut v___f_7136_: *mut LeanObject,
    mut v_x_7137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7142_: u8 = 0;
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7147_: u8 = 0;
    let mut v_a_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7151_: u8 = 0;
    let mut v___x_7152_: u8 = 0;
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: u8 = 0;
    let mut v___x_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7137_) == 0 {
                    lean_dec_ref(v___f_7136_);
                    lean_dec(v_pendingIncompleteChunk_7133_);
                    lean_dec(v_knownSize_7132_);
                    lean_dec(v_interestWaiter_7130_);
                    lean_dec(v_pendingProducer_7129_);
                    v_a_7139_ = lean_ctor_get(v_x_7137_, 0);
                    v_isSharedCheck_7147_ = (!lean_is_exclusive(v_x_7137_)) as u8;
                    if v_isSharedCheck_7147_ == 0 {
                        v___x_7141_ = v_x_7137_;
                        v_isShared_7142_ = v_isSharedCheck_7147_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7139_);
                        lean_dec(v_x_7137_);
                        v___x_7141_ = lean_box(0);
                        v_isShared_7142_ = v_isSharedCheck_7147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7148_ = lean_ctor_get(v_x_7137_, 0);
                    v_isSharedCheck_7174_ = (!lean_is_exclusive(v_x_7137_)) as u8;
                    if v_isSharedCheck_7174_ == 0 {
                        v___x_7150_ = v_x_7137_;
                        v_isShared_7151_ = v_isSharedCheck_7174_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7148_);
                        lean_dec(v_x_7137_);
                        v___x_7150_ = lean_box(0);
                        v_isShared_7151_ = v_isSharedCheck_7174_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7142_ == 0 {
                    v___x_7144_ = v___x_7141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7146_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7146_, 0, v_a_7139_);
                    v___x_7144_ = v_reuseFailAlloc_7146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7145_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7145_, 0, v___x_7144_);
                return v___x_7145_;
            }
            3 => {
                v___x_7152_ = (lean_unbox(v_a_7148_) as u8);
                if v___x_7152_ == 0 {
                    lean_dec_ref(v___f_7136_);
                    v___x_7153_ = lean_box(0);
                    v___x_7154_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v___x_7154_, 0, v_pendingProducer_7129_);
                    lean_ctor_set(v___x_7154_, 1, v___x_7153_);
                    lean_ctor_set(v___x_7154_, 2, v_interestWaiter_7130_);
                    lean_ctor_set(v___x_7154_, 3, v_knownSize_7132_);
                    lean_ctor_set(v___x_7154_, 4, v_pendingIncompleteChunk_7133_);
                    lean_ctor_set_uint8(
                        v___x_7154_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_7131_,
                    );
                    v___x_7155_ = lean_st_ref_set(v___y_7134_, v___x_7154_);
                    lean_inc(v_a_7148_);
                    v___f_7156_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__5___boxed as *mut core::ffi::c_void, 3, 1);
                    lean_closure_set(v___f_7156_, 0, v_a_7148_);
                    if v_isShared_7151_ == 0 {
                        lean_ctor_set(v___x_7150_, 0, v___x_7155_);
                        v___x_7158_ = v___x_7150_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7163_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7163_, 0, v___x_7155_);
                        v___x_7158_ = v_reuseFailAlloc_7163_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_7148_);
                    v___x_7164_ = lean_box(0);
                    v___x_7165_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_decreaseKnownSize(v_knownSize_7132_, v_chunk_7135_);
                    v___x_7166_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v___x_7166_, 0, v_pendingProducer_7129_);
                    lean_ctor_set(v___x_7166_, 1, v___x_7164_);
                    lean_ctor_set(v___x_7166_, 2, v_interestWaiter_7130_);
                    lean_ctor_set(v___x_7166_, 3, v___x_7165_);
                    lean_ctor_set(v___x_7166_, 4, v_pendingIncompleteChunk_7133_);
                    lean_ctor_set_uint8(
                        v___x_7166_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_7131_,
                    );
                    v___x_7167_ = lean_st_ref_set(v___y_7134_, v___x_7166_);
                    if v_isShared_7151_ == 0 {
                        lean_ctor_set(v___x_7150_, 0, v___x_7167_);
                        v___x_7169_ = v___x_7150_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7173_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7173_, 0, v___x_7167_);
                        v___x_7169_ = v_reuseFailAlloc_7173_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7159_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7159_, 0, v___x_7158_);
                v___x_7160_ = lean_unsigned_to_nat(0);
                v___x_7161_ = (lean_unbox(v_a_7148_) as u8);
                lean_dec(v_a_7148_);
                v___x_7162_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7160_,
                    v___x_7161_,
                    v___x_7159_,
                    v___f_7156_,
                );
                return v___x_7162_;
            }
            5 => {
                v___x_7170_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7170_, 0, v___x_7169_);
                v___x_7171_ = lean_unsigned_to_nat(0);
                v___x_7172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7171_,
                    v_closed_7131_,
                    v___x_7170_,
                    v___f_7136_,
                );
                return v___x_7172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed(
    mut v_pendingProducer_7175_: *mut LeanObject,
    mut v_interestWaiter_7176_: *mut LeanObject,
    mut v_closed_7177_: *mut LeanObject,
    mut v_knownSize_7178_: *mut LeanObject,
    mut v_pendingIncompleteChunk_7179_: *mut LeanObject,
    mut v___y_7180_: *mut LeanObject,
    mut v_chunk_7181_: *mut LeanObject,
    mut v___f_7182_: *mut LeanObject,
    mut v_x_7183_: *mut LeanObject,
    mut v___y_7184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_7185_: u8 = 0;
    let mut v_res_7186_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_7185_ = (lean_unbox(v_closed_7177_) as u8);
    v_res_7186_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6(
        v_pendingProducer_7175_,
        v_interestWaiter_7176_,
        v_closed_boxed_7185_,
        v_knownSize_7178_,
        v_pendingIncompleteChunk_7179_,
        v___y_7180_,
        v_chunk_7181_,
        v___f_7182_,
        v_x_7183_,
    );
    lean_dec_ref(v_chunk_7181_);
    lean_dec(v___y_7180_);
    return v_res_7186_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(
    mut v_chunk_7205_: *mut LeanObject,
    mut v___y_7206_: *mut LeanObject,
    mut v_a_7207_: *mut LeanObject,
    mut v___f_7208_: *mut LeanObject,
    mut v_x_7209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7214_: u8 = 0;
    let mut v___x_7216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7219_: u8 = 0;
    let mut v_a_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7223_: u8 = 0;
    let mut v_closed_7224_: u8 = 0;
    let mut v_pendingConsumer_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7233_: u8 = 0;
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: u8 = 0;
    let mut v___f_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7248_: u8 = 0;
    let mut v_pendingProducer_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7255_: u8 = 0;
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7268_: u8 = 0;
    let mut v_unused_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7209_) == 0 {
                    lean_dec_ref(v___f_7208_);
                    lean_dec(v_a_7207_);
                    lean_dec_ref(v_chunk_7205_);
                    v_a_7211_ = lean_ctor_get(v_x_7209_, 0);
                    v_isSharedCheck_7219_ = (!lean_is_exclusive(v_x_7209_)) as u8;
                    if v_isSharedCheck_7219_ == 0 {
                        v___x_7213_ = v_x_7209_;
                        v_isShared_7214_ = v_isSharedCheck_7219_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7211_);
                        lean_dec(v_x_7209_);
                        v___x_7213_ = lean_box(0);
                        v_isShared_7214_ = v_isSharedCheck_7219_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7220_ = lean_ctor_get(v_x_7209_, 0);
                    v_isSharedCheck_7273_ = (!lean_is_exclusive(v_x_7209_)) as u8;
                    if v_isSharedCheck_7273_ == 0 {
                        v___x_7222_ = v_x_7209_;
                        v_isShared_7223_ = v_isSharedCheck_7273_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7220_);
                        lean_dec(v_x_7209_);
                        v___x_7222_ = lean_box(0);
                        v_isShared_7223_ = v_isSharedCheck_7273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7214_ == 0 {
                    v___x_7216_ = v___x_7213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7218_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7218_, 0, v_a_7211_);
                    v___x_7216_ = v_reuseFailAlloc_7218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7217_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7217_, 0, v___x_7216_);
                return v___x_7217_;
            }
            3 => {
                v_closed_7224_ = lean_ctor_get_uint8(
                    v_a_7220_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                if v_closed_7224_ == 0 {
                    v_pendingConsumer_7225_ = lean_ctor_get(v_a_7220_, 1);
                    lean_inc(v_pendingConsumer_7225_);
                    if lean_obj_tag(v_pendingConsumer_7225_) == 1 {
                        lean_dec_ref(v___f_7208_);
                        lean_dec(v_a_7207_);
                        v_pendingProducer_7226_ = lean_ctor_get(v_a_7220_, 0);
                        lean_inc(v_pendingProducer_7226_);
                        v_interestWaiter_7227_ = lean_ctor_get(v_a_7220_, 2);
                        lean_inc(v_interestWaiter_7227_);
                        v_knownSize_7228_ = lean_ctor_get(v_a_7220_, 3);
                        lean_inc(v_knownSize_7228_);
                        v_pendingIncompleteChunk_7229_ = lean_ctor_get(v_a_7220_, 4);
                        lean_inc(v_pendingIncompleteChunk_7229_);
                        lean_dec(v_a_7220_);
                        v_val_7230_ = lean_ctor_get(v_pendingConsumer_7225_, 0);
                        v_isSharedCheck_7248_ = (!lean_is_exclusive(v_pendingConsumer_7225_)) as u8;
                        if v_isSharedCheck_7248_ == 0 {
                            v___x_7232_ = v_pendingConsumer_7225_;
                            v_isShared_7233_ = v_isSharedCheck_7248_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_7230_);
                            lean_dec(v_pendingConsumer_7225_);
                            v___x_7232_ = lean_box(0);
                            v_isShared_7233_ = v_isSharedCheck_7248_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_pendingProducer_7249_ = lean_ctor_get(v_a_7220_, 0);
                        if lean_obj_tag(v_pendingProducer_7249_) == 0 {
                            v_interestWaiter_7250_ = lean_ctor_get(v_a_7220_, 2);
                            v_knownSize_7251_ = lean_ctor_get(v_a_7220_, 3);
                            v_pendingIncompleteChunk_7252_ = lean_ctor_get(v_a_7220_, 4);
                            v_isSharedCheck_7268_ = (!lean_is_exclusive(v_a_7220_)) as u8;
                            if v_isSharedCheck_7268_ == 0 {
                                v_unused_7269_ = lean_ctor_get(v_a_7220_, 1);
                                lean_dec(v_unused_7269_);
                                v_unused_7270_ = lean_ctor_get(v_a_7220_, 0);
                                lean_dec(v_unused_7270_);
                                v___x_7254_ = v_a_7220_;
                                v_isShared_7255_ = v_isSharedCheck_7268_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_pendingIncompleteChunk_7252_);
                                lean_inc(v_knownSize_7251_);
                                lean_inc(v_interestWaiter_7250_);
                                lean_dec(v_a_7220_);
                                v___x_7254_ = lean_box(0);
                                v_isShared_7255_ = v_isSharedCheck_7268_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_pendingConsumer_7225_);
                            lean_del_object(v___x_7222_);
                            lean_dec(v_a_7220_);
                            lean_dec_ref(v___f_7208_);
                            lean_dec(v_a_7207_);
                            lean_dec_ref(v_chunk_7205_);
                            v___x_7271_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__5;
                            return v___x_7271_;
                        }
                    }
                } else {
                    lean_del_object(v___x_7222_);
                    lean_dec(v_a_7220_);
                    lean_dec_ref(v___f_7208_);
                    lean_dec(v_a_7207_);
                    lean_dec_ref(v_chunk_7205_);
                    v___x_7272_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__8;
                    return v___x_7272_;
                }
            }
            4 => {
                lean_inc_ref(v_chunk_7205_);
                if v_isShared_7233_ == 0 {
                    lean_ctor_set(v___x_7232_, 0, v_chunk_7205_);
                    v___x_7235_ = v___x_7232_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7247_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7247_, 0, v_chunk_7205_);
                    v___x_7235_ = v_reuseFailAlloc_7247_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7236_ =
                    l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_Consumer_resolve(
                        v_val_7230_,
                        v___x_7235_,
                    );
                lean_dec(v_val_7230_);
                v___f_7237_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___closed__0;
                v___x_7238_ = lean_box((v_closed_7224_) as usize);
                lean_inc(v___y_7206_);
                v___f_7239_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__6___boxed as *mut core::ffi::c_void, 10, 8);
                lean_closure_set(v___f_7239_, 0, v_pendingProducer_7226_);
                lean_closure_set(v___f_7239_, 1, v_interestWaiter_7227_);
                lean_closure_set(v___f_7239_, 2, v___x_7238_);
                lean_closure_set(v___f_7239_, 3, v_knownSize_7228_);
                lean_closure_set(v___f_7239_, 4, v_pendingIncompleteChunk_7229_);
                lean_closure_set(v___f_7239_, 5, v___y_7206_);
                lean_closure_set(v___f_7239_, 6, v_chunk_7205_);
                lean_closure_set(v___f_7239_, 7, v___f_7237_);
                v___x_7240_ = lean_box((v___x_7236_) as usize);
                if v_isShared_7223_ == 0 {
                    lean_ctor_set(v___x_7222_, 0, v___x_7240_);
                    v___x_7242_ = v___x_7222_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7246_, 0, v___x_7240_);
                    v___x_7242_ = v_reuseFailAlloc_7246_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7243_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7243_, 0, v___x_7242_);
                v___x_7244_ = lean_unsigned_to_nat(0);
                v___x_7245_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7244_,
                    v_closed_7224_,
                    v___x_7243_,
                    v___f_7239_,
                );
                return v___x_7245_;
            }
            7 => {
                v___x_7256_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7256_, 0, v_chunk_7205_);
                lean_ctor_set(v___x_7256_, 1, v_a_7207_);
                v___x_7257_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7257_, 0, v___x_7256_);
                if v_isShared_7255_ == 0 {
                    lean_ctor_set(v___x_7254_, 0, v___x_7257_);
                    v___x_7259_ = v___x_7254_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7267_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 0, v___x_7257_);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 1, v_pendingConsumer_7225_);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 2, v_interestWaiter_7250_);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 3, v_knownSize_7251_);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 4, v_pendingIncompleteChunk_7252_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7267_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_7224_,
                    );
                    v___x_7259_ = v_reuseFailAlloc_7267_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7260_ = lean_st_ref_set(v___y_7206_, v___x_7259_);
                if v_isShared_7223_ == 0 {
                    lean_ctor_set(v___x_7222_, 0, v___x_7260_);
                    v___x_7262_ = v___x_7222_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7266_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7266_, 0, v___x_7260_);
                    v___x_7262_ = v_reuseFailAlloc_7266_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7263_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7263_, 0, v___x_7262_);
                v___x_7264_ = lean_unsigned_to_nat(0);
                v___x_7265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7264_,
                    v_closed_7224_,
                    v___x_7263_,
                    v___f_7208_,
                );
                return v___x_7265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed(
    mut v_chunk_7274_: *mut LeanObject,
    mut v___y_7275_: *mut LeanObject,
    mut v_a_7276_: *mut LeanObject,
    mut v___f_7277_: *mut LeanObject,
    mut v_x_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7280_: *mut LeanObject = core::ptr::null_mut();
    v_res_7280_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7(
        v_chunk_7274_,
        v___y_7275_,
        v_a_7276_,
        v___f_7277_,
        v_x_7278_,
    );
    lean_dec(v___y_7275_);
    return v_res_7280_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(
    mut v___y_7281_: *mut LeanObject,
    mut v___f_7282_: *mut LeanObject,
    mut v_x_7283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7288_: u8 = 0;
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7293_: u8 = 0;
    let mut v___x_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7296_: u8 = 0;
    let mut v___x_7297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: u8 = 0;
    let mut v___x_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7305_: u8 = 0;
    let mut v_unused_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7283_) == 0 {
                    lean_dec_ref(v___f_7282_);
                    v_a_7285_ = lean_ctor_get(v_x_7283_, 0);
                    v_isSharedCheck_7293_ = (!lean_is_exclusive(v_x_7283_)) as u8;
                    if v_isSharedCheck_7293_ == 0 {
                        v___x_7287_ = v_x_7283_;
                        v_isShared_7288_ = v_isSharedCheck_7293_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7285_);
                        lean_dec(v_x_7283_);
                        v___x_7287_ = lean_box(0);
                        v_isShared_7288_ = v_isSharedCheck_7293_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_7305_ = (!lean_is_exclusive(v_x_7283_)) as u8;
                    if v_isSharedCheck_7305_ == 0 {
                        v_unused_7306_ = lean_ctor_get(v_x_7283_, 0);
                        lean_dec(v_unused_7306_);
                        v___x_7295_ = v_x_7283_;
                        v_isShared_7296_ = v_isSharedCheck_7305_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_7283_);
                        v___x_7295_ = lean_box(0);
                        v_isShared_7296_ = v_isSharedCheck_7305_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7288_ == 0 {
                    v___x_7290_ = v___x_7287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7292_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7292_, 0, v_a_7285_);
                    v___x_7290_ = v_reuseFailAlloc_7292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7291_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7291_, 0, v___x_7290_);
                return v___x_7291_;
            }
            3 => {
                v___x_7297_ = lean_st_ref_get(v___y_7281_);
                if v_isShared_7296_ == 0 {
                    lean_ctor_set(v___x_7295_, 0, v___x_7297_);
                    v___x_7299_ = v___x_7295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7304_, 0, v___x_7297_);
                    v___x_7299_ = v_reuseFailAlloc_7304_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7300_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7300_, 0, v___x_7299_);
                v___x_7301_ = lean_unsigned_to_nat(0);
                v___x_7302_ = 0;
                v___x_7303_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7301_,
                    v___x_7302_,
                    v___x_7300_,
                    v___f_7282_,
                );
                return v___x_7303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed(
    mut v___y_7307_: *mut LeanObject,
    mut v___f_7308_: *mut LeanObject,
    mut v_x_7309_: *mut LeanObject,
    mut v___y_7310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7311_: *mut LeanObject = core::ptr::null_mut();
    v_res_7311_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8(
        v___y_7307_,
        v___f_7308_,
        v_x_7309_,
    );
    lean_dec(v___y_7307_);
    return v_res_7311_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(
    mut v_chunk_7312_: *mut LeanObject,
    mut v_a_7313_: *mut LeanObject,
    mut v___f_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: u8 = 0;
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    v___x_7317_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_7315_);
    lean_inc_n(v___y_7315_, 2);
    v___f_7318_ = lean_alloc_closure(
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__7___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_7318_, 0, v_chunk_7312_);
    lean_closure_set(v___f_7318_, 1, v___y_7315_);
    lean_closure_set(v___f_7318_, 2, v_a_7313_);
    lean_closure_set(v___f_7318_, 3, v___f_7314_);
    v___f_7319_ = lean_alloc_closure(
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__8___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7319_, 0, v___y_7315_);
    lean_closure_set(v___f_7319_, 1, v___f_7318_);
    v___x_7320_ = lean_unsigned_to_nat(0);
    v___x_7321_ = 0;
    v___x_7322_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7320_,
        v___x_7321_,
        v___x_7317_,
        v___f_7319_,
    );
    return v___x_7322_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed(
    mut v_chunk_7323_: *mut LeanObject,
    mut v_a_7324_: *mut LeanObject,
    mut v___f_7325_: *mut LeanObject,
    mut v___y_7326_: *mut LeanObject,
    mut v___y_7327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7328_: *mut LeanObject = core::ptr::null_mut();
    v_res_7328_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9(
        v_chunk_7323_,
        v_a_7324_,
        v___f_7325_,
        v___y_7326_,
    );
    lean_dec(v___y_7326_);
    return v_res_7328_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(
    mut v_a_7334_: *mut LeanObject,
    mut v___f_7335_: *mut LeanObject,
    mut v___f_7336_: *mut LeanObject,
    mut v_stream_7337_: *mut LeanObject,
    mut v_chunk_7338_: *mut LeanObject,
    mut v___f_7339_: *mut LeanObject,
    mut v_x_7340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7345_: u8 = 0;
    let mut v___x_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7350_: u8 = 0;
    let mut v_a_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7355_: u8 = 0;
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7360_: u8 = 0;
    let mut v_a_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: u8 = 0;
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: u8 = 0;
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7340_) == 0 {
                    lean_dec_ref(v___f_7339_);
                    lean_dec_ref(v_chunk_7338_);
                    lean_dec_ref(v_stream_7337_);
                    lean_dec_ref(v___f_7336_);
                    lean_dec_ref(v___f_7335_);
                    v_a_7342_ = lean_ctor_get(v_x_7340_, 0);
                    v_isSharedCheck_7350_ = (!lean_is_exclusive(v_x_7340_)) as u8;
                    if v_isSharedCheck_7350_ == 0 {
                        v___x_7344_ = v_x_7340_;
                        v_isShared_7345_ = v_isSharedCheck_7350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7342_);
                        lean_dec(v_x_7340_);
                        v___x_7344_ = lean_box(0);
                        v_isShared_7345_ = v_isSharedCheck_7350_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7351_ = lean_ctor_get(v_x_7340_, 0);
                    lean_inc(v_a_7351_);
                    lean_dec_ref_known(v_x_7340_, 1);
                    if lean_obj_tag(v_a_7351_) == 0 {
                        lean_dec_ref(v___f_7339_);
                        lean_dec_ref(v_chunk_7338_);
                        lean_dec_ref(v_stream_7337_);
                        lean_dec_ref(v___f_7336_);
                        lean_dec_ref(v___f_7335_);
                        v_a_7352_ = lean_ctor_get(v_a_7351_, 0);
                        v_isSharedCheck_7360_ = (!lean_is_exclusive(v_a_7351_)) as u8;
                        if v_isSharedCheck_7360_ == 0 {
                            v___x_7354_ = v_a_7351_;
                            v_isShared_7355_ = v_isSharedCheck_7360_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7352_);
                            lean_dec(v_a_7351_);
                            v___x_7354_ = lean_box(0);
                            v_isShared_7355_ = v_isSharedCheck_7360_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7361_ = lean_ctor_get(v_a_7351_, 0);
                        lean_inc(v_a_7361_);
                        lean_dec_ref_known(v_a_7351_, 1);
                        if lean_obj_tag(v_a_7361_) == 0 {
                            lean_dec_ref(v___f_7339_);
                            lean_dec_ref(v_chunk_7338_);
                            lean_dec_ref(v_stream_7337_);
                            v___x_7362_ = lean_io_promise_result_opt(v_a_7334_);
                            v___x_7363_ = lean_unsigned_to_nat(0);
                            v___x_7364_ = 0;
                            v___x_7365_ =
                                lean_task_map(v___f_7335_, v___x_7362_, v___x_7363_, v___x_7364_);
                            v___x_7366_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_7366_, 0, v___x_7365_);
                            v___x_7367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7363_, v___x_7364_, v___x_7366_, v___f_7336_);
                            return v___x_7367_;
                        } else {
                            lean_dec_ref(v___f_7336_);
                            lean_dec_ref(v___f_7335_);
                            v_val_7368_ = lean_ctor_get(v_a_7361_, 0);
                            lean_inc(v_val_7368_);
                            lean_dec_ref_known(v_a_7361_, 1);
                            v___x_7369_ = (lean_unbox(v_val_7368_) as u8);
                            lean_dec(v_val_7368_);
                            if v___x_7369_ == 0 {
                                lean_dec_ref(v___f_7339_);
                                v___x_7370_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_7337_, v_chunk_7338_);
                                return v___x_7370_;
                            } else {
                                lean_dec_ref(v_chunk_7338_);
                                lean_dec_ref(v_stream_7337_);
                                v___x_7371_ = lean_box(0);
                                v___x_7372_ = lean_apply_2(v___f_7339_, v___x_7371_, lean_box(0));
                                return v___x_7372_;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7345_ == 0 {
                    v___x_7347_ = v___x_7344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7349_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7349_, 0, v_a_7342_);
                    v___x_7347_ = v_reuseFailAlloc_7349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7348_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7348_, 0, v___x_7347_);
                return v___x_7348_;
            }
            3 => {
                if v_isShared_7355_ == 0 {
                    v___x_7357_ = v___x_7354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7359_, 0, v_a_7352_);
                    v___x_7357_ = v_reuseFailAlloc_7359_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7358_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7358_, 0, v___x_7357_);
                return v___x_7358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed(
    mut v_a_7373_: *mut LeanObject,
    mut v___f_7374_: *mut LeanObject,
    mut v___f_7375_: *mut LeanObject,
    mut v_stream_7376_: *mut LeanObject,
    mut v_chunk_7377_: *mut LeanObject,
    mut v___f_7378_: *mut LeanObject,
    mut v_x_7379_: *mut LeanObject,
    mut v___y_7380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7381_: *mut LeanObject = core::ptr::null_mut();
    v_res_7381_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10(
        v_a_7373_,
        v___f_7374_,
        v___f_7375_,
        v_stream_7376_,
        v_chunk_7377_,
        v___f_7378_,
        v_x_7379_,
    );
    lean_dec(v_a_7373_);
    return v_res_7381_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(
    mut v_chunk_7382_: *mut LeanObject,
    mut v___f_7383_: *mut LeanObject,
    mut v_stream_7384_: *mut LeanObject,
    mut v___f_7385_: *mut LeanObject,
    mut v___f_7386_: *mut LeanObject,
    mut v___f_7387_: *mut LeanObject,
    mut v_x_7388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7393_: u8 = 0;
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7398_: u8 = 0;
    let mut v_a_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: u8 = 0;
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7388_) == 0 {
                    lean_dec_ref(v___f_7387_);
                    lean_dec_ref(v___f_7386_);
                    lean_dec_ref(v___f_7385_);
                    lean_dec_ref(v_stream_7384_);
                    lean_dec_ref(v___f_7383_);
                    lean_dec_ref(v_chunk_7382_);
                    v_a_7390_ = lean_ctor_get(v_x_7388_, 0);
                    v_isSharedCheck_7398_ = (!lean_is_exclusive(v_x_7388_)) as u8;
                    if v_isSharedCheck_7398_ == 0 {
                        v___x_7392_ = v_x_7388_;
                        v_isShared_7393_ = v_isSharedCheck_7398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7390_);
                        lean_dec(v_x_7388_);
                        v___x_7392_ = lean_box(0);
                        v_isShared_7393_ = v_isSharedCheck_7398_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7399_ = lean_ctor_get(v_x_7388_, 0);
                    lean_inc_n(v_a_7399_, 2);
                    lean_dec_ref_known(v_x_7388_, 1);
                    lean_inc_ref(v_chunk_7382_);
                    v___f_7400_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__9___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_7400_, 0, v_chunk_7382_);
                    lean_closure_set(v___f_7400_, 1, v_a_7399_);
                    lean_closure_set(v___f_7400_, 2, v___f_7383_);
                    lean_inc_ref(v_stream_7384_);
                    v___x_7401_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(v_stream_7384_, v___f_7400_);
                    v___f_7402_ = lean_alloc_closure(l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__10___boxed as *mut core::ffi::c_void, 8, 6);
                    lean_closure_set(v___f_7402_, 0, v_a_7399_);
                    lean_closure_set(v___f_7402_, 1, v___f_7385_);
                    lean_closure_set(v___f_7402_, 2, v___f_7386_);
                    lean_closure_set(v___f_7402_, 3, v_stream_7384_);
                    lean_closure_set(v___f_7402_, 4, v_chunk_7382_);
                    lean_closure_set(v___f_7402_, 5, v___f_7387_);
                    v___x_7403_ = lean_unsigned_to_nat(0);
                    v___x_7404_ = 0;
                    v___x_7405_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_7403_,
                            v___x_7404_,
                            v___x_7401_,
                            v___f_7402_,
                        );
                    return v___x_7405_;
                }
            }
            1 => {
                if v_isShared_7393_ == 0 {
                    v___x_7395_ = v___x_7392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7397_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7397_, 0, v_a_7390_);
                    v___x_7395_ = v_reuseFailAlloc_7397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7396_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7396_, 0, v___x_7395_);
                return v___x_7396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed(
    mut v_chunk_7406_: *mut LeanObject,
    mut v___f_7407_: *mut LeanObject,
    mut v_stream_7408_: *mut LeanObject,
    mut v___f_7409_: *mut LeanObject,
    mut v___f_7410_: *mut LeanObject,
    mut v___f_7411_: *mut LeanObject,
    mut v_x_7412_: *mut LeanObject,
    mut v___y_7413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7414_: *mut LeanObject = core::ptr::null_mut();
    v_res_7414_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11(
        v_chunk_7406_,
        v___f_7407_,
        v_stream_7408_,
        v___f_7409_,
        v___f_7410_,
        v___f_7411_,
        v_x_7412_,
    );
    return v_res_7414_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(
    mut v_stream_7415_: *mut LeanObject,
    mut v_chunk_7416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: u8 = 0;
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    v___x_7418_ = lean_io_promise_new();
    v___f_7419_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__0;
    v___f_7420_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__1;
    v___f_7421_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__2;
    v___f_7422_ =
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___closed__3;
    v___f_7423_ = lean_alloc_closure(
        l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___lam__11___boxed
            as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___f_7423_, 0, v_chunk_7416_);
    lean_closure_set(v___f_7423_, 1, v___f_7419_);
    lean_closure_set(v___f_7423_, 2, v_stream_7415_);
    lean_closure_set(v___f_7423_, 3, v___f_7422_);
    lean_closure_set(v___f_7423_, 4, v___f_7421_);
    lean_closure_set(v___f_7423_, 5, v___f_7420_);
    v___x_7424_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7424_, 0, v___x_7418_);
    v___x_7425_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7425_, 0, v___x_7424_);
    v___x_7426_ = lean_unsigned_to_nat(0);
    v___x_7427_ = 0;
    v___x_7428_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7426_,
        v___x_7427_,
        v___x_7425_,
        v___f_7423_,
    );
    return v___x_7428_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27___boxed(
    mut v_stream_7429_: *mut LeanObject,
    mut v_chunk_7430_: *mut LeanObject,
    mut v_a_7431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7432_: *mut LeanObject = core::ptr::null_mut();
    v_res_7432_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(
        v_stream_7429_,
        v_chunk_7430_,
    );
    return v_res_7432_;
}
pub unsafe fn l_Std_Http_Body_Stream_send___lam__0(
    mut v_stream_7433_: *mut LeanObject,
    mut v_x_7434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7439_: u8 = 0;
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7444_: u8 = 0;
    let mut v_a_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7449_: u8 = 0;
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7454_: u8 = 0;
    let mut v_a_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: u8 = 0;
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7434_) == 0 {
                    lean_dec_ref(v_stream_7433_);
                    v_a_7436_ = lean_ctor_get(v_x_7434_, 0);
                    v_isSharedCheck_7444_ = (!lean_is_exclusive(v_x_7434_)) as u8;
                    if v_isSharedCheck_7444_ == 0 {
                        v___x_7438_ = v_x_7434_;
                        v_isShared_7439_ = v_isSharedCheck_7444_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7436_);
                        lean_dec(v_x_7434_);
                        v___x_7438_ = lean_box(0);
                        v_isShared_7439_ = v_isSharedCheck_7444_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7445_ = lean_ctor_get(v_x_7434_, 0);
                    lean_inc(v_a_7445_);
                    lean_dec_ref_known(v_x_7434_, 1);
                    if lean_obj_tag(v_a_7445_) == 0 {
                        lean_dec_ref(v_stream_7433_);
                        v_a_7446_ = lean_ctor_get(v_a_7445_, 0);
                        v_isSharedCheck_7454_ = (!lean_is_exclusive(v_a_7445_)) as u8;
                        if v_isSharedCheck_7454_ == 0 {
                            v___x_7448_ = v_a_7445_;
                            v_isShared_7449_ = v_isSharedCheck_7454_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7446_);
                            lean_dec(v_a_7445_);
                            v___x_7448_ = lean_box(0);
                            v_isShared_7449_ = v_isSharedCheck_7454_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7455_ = lean_ctor_get(v_a_7445_, 0);
                        lean_inc(v_a_7455_);
                        lean_dec_ref_known(v_a_7445_, 1);
                        if lean_obj_tag(v_a_7455_) == 0 {
                            lean_dec_ref(v_stream_7433_);
                            v___x_7456_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                            return v___x_7456_;
                        } else {
                            v_val_7457_ = lean_ctor_get(v_a_7455_, 0);
                            lean_inc(v_val_7457_);
                            lean_dec_ref_known(v_a_7455_, 1);
                            v_data_7458_ = lean_ctor_get(v_val_7457_, 0);
                            v_extensions_7459_ = lean_ctor_get(v_val_7457_, 1);
                            v___x_7460_ = l_ByteArray_isEmpty(v_data_7458_);
                            if v___x_7460_ == 0 {
                                v___x_7461_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_7433_, v_val_7457_);
                                return v___x_7461_;
                            } else {
                                v___x_7462_ = lean_array_get_size(v_extensions_7459_);
                                v___x_7463_ = lean_unsigned_to_nat(0);
                                v___x_7464_ = lean_nat_dec_eq(v___x_7462_, v___x_7463_);
                                if v___x_7464_ == 0 {
                                    v___x_7465_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_send_x27(v_stream_7433_, v_val_7457_);
                                    return v___x_7465_;
                                } else {
                                    lean_dec(v_val_7457_);
                                    lean_dec_ref(v_stream_7433_);
                                    v___x_7466_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                                    return v___x_7466_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7439_ == 0 {
                    v___x_7441_ = v___x_7438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7443_, 0, v_a_7436_);
                    v___x_7441_ = v_reuseFailAlloc_7443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7442_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7442_, 0, v___x_7441_);
                return v___x_7442_;
            }
            3 => {
                if v_isShared_7449_ == 0 {
                    v___x_7451_ = v___x_7448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7453_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7453_, 0, v_a_7446_);
                    v___x_7451_ = v_reuseFailAlloc_7453_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7452_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7452_, 0, v___x_7451_);
                return v___x_7452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_send___lam__0___boxed(
    mut v_stream_7467_: *mut LeanObject,
    mut v_x_7468_: *mut LeanObject,
    mut v___y_7469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7470_: *mut LeanObject = core::ptr::null_mut();
    v_res_7470_ = l_Std_Http_Body_Stream_send___lam__0(v_stream_7467_, v_x_7468_);
    return v_res_7470_;
}
pub unsafe fn l_Std_Http_Body_Stream_send(
    mut v_stream_7471_: *mut LeanObject,
    mut v_chunk_7472_: *mut LeanObject,
    mut v_incomplete_7473_: u8,
) -> *mut LeanObject {
    let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: u8 = 0;
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_stream_7471_);
    v___x_7475_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Stream_collapseForSend(
        v_stream_7471_,
        v_chunk_7472_,
        v_incomplete_7473_,
    );
    v___f_7476_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_send___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7476_, 0, v_stream_7471_);
    v___x_7477_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7477_, 0, v___x_7475_);
    v___x_7478_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7478_, 0, v___x_7477_);
    v___x_7479_ = lean_unsigned_to_nat(0);
    v___x_7480_ = 0;
    v___x_7481_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7479_,
        v___x_7480_,
        v___x_7478_,
        v___f_7476_,
    );
    return v___x_7481_;
}
pub unsafe fn l_Std_Http_Body_Stream_send___boxed(
    mut v_stream_7482_: *mut LeanObject,
    mut v_chunk_7483_: *mut LeanObject,
    mut v_incomplete_7484_: *mut LeanObject,
    mut v_a_7485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_incomplete_boxed_7486_: u8 = 0;
    let mut v_res_7487_: *mut LeanObject = core::ptr::null_mut();
    v_incomplete_boxed_7486_ = (lean_unbox(v_incomplete_7484_) as u8);
    v_res_7487_ =
        l_Std_Http_Body_Stream_send(v_stream_7482_, v_chunk_7483_, v_incomplete_boxed_7486_);
    return v_res_7487_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(
    mut v_x_7488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7491_: u8 = 0;
    let mut v___x_7492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7498_: u8 = 0;
    let mut v___x_7500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7503_: u8 = 0;
    let mut v_a_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: u8 = 0;
    let mut v___x_7507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7488_) == 0 {
                    v_a_7495_ = lean_ctor_get(v_x_7488_, 0);
                    v_isSharedCheck_7503_ = (!lean_is_exclusive(v_x_7488_)) as u8;
                    if v_isSharedCheck_7503_ == 0 {
                        v___x_7497_ = v_x_7488_;
                        v_isShared_7498_ = v_isSharedCheck_7503_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7495_);
                        lean_dec(v_x_7488_);
                        v___x_7497_ = lean_box(0);
                        v_isShared_7498_ = v_isSharedCheck_7503_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7504_ = lean_ctor_get(v_x_7488_, 0);
                    lean_inc(v_a_7504_);
                    lean_dec_ref_known(v_x_7488_, 1);
                    v_pendingConsumer_7505_ = lean_ctor_get(v_a_7504_, 1);
                    lean_inc(v_pendingConsumer_7505_);
                    lean_dec(v_a_7504_);
                    if lean_obj_tag(v_pendingConsumer_7505_) == 0 {
                        v___x_7506_ = 0;
                        v___y_7491_ = v___x_7506_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v_pendingConsumer_7505_, 1);
                        v___x_7507_ = 1;
                        v___y_7491_ = v___x_7507_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7492_ = lean_box((v___y_7491_) as usize);
                v___x_7493_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7493_, 0, v___x_7492_);
                v___x_7494_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7494_, 0, v___x_7493_);
                return v___x_7494_;
            }
            2 => {
                if v_isShared_7498_ == 0 {
                    v___x_7500_ = v___x_7497_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7502_, 0, v_a_7495_);
                    v___x_7500_ = v_reuseFailAlloc_7502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7501_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7501_, 0, v___x_7500_);
                return v___x_7501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0___boxed(
    mut v_x_7508_: *mut LeanObject,
    mut v___y_7509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7510_: *mut LeanObject = core::ptr::null_mut();
    v_res_7510_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___lam__0(v_x_7508_);
    return v_res_7510_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(
    mut v_a_7512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: u8 = 0;
    let mut v___x_7520_: *mut LeanObject = core::ptr::null_mut();
    v___x_7514_ = lean_st_ref_get(v_a_7512_);
    v___f_7515_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___closed__0;
    v___x_7516_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7516_, 0, v___x_7514_);
    v___x_7517_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7517_, 0, v___x_7516_);
    v___x_7518_ = lean_unsigned_to_nat(0);
    v___x_7519_ = 0;
    v___x_7520_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7518_,
        v___x_7519_,
        v___x_7517_,
        v___f_7515_,
    );
    return v___x_7520_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0___boxed(
    mut v_a_7521_: *mut LeanObject,
    mut v___y_7522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7523_: *mut LeanObject = core::ptr::null_mut();
    v_res_7523_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v_a_7521_);
    lean_dec(v_a_7521_);
    return v_res_7523_;
}
pub unsafe fn l_Std_Http_Body_Stream_hasInterest___lam__0(
    mut v___y_7524_: *mut LeanObject,
    mut v_x_7525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7530_: u8 = 0;
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7535_: u8 = 0;
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7525_) == 0 {
                    v_a_7527_ = lean_ctor_get(v_x_7525_, 0);
                    v_isSharedCheck_7535_ = (!lean_is_exclusive(v_x_7525_)) as u8;
                    if v_isSharedCheck_7535_ == 0 {
                        v___x_7529_ = v_x_7525_;
                        v_isShared_7530_ = v_isSharedCheck_7535_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7527_);
                        lean_dec(v_x_7525_);
                        v___x_7529_ = lean_box(0);
                        v_isShared_7530_ = v_isSharedCheck_7535_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_7525_, 1);
                    v___x_7536_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_hasInterest_x27___at___00Std_Http_Body_Stream_hasInterest_spec__0(v___y_7524_);
                    return v___x_7536_;
                }
            }
            1 => {
                if v_isShared_7530_ == 0 {
                    v___x_7532_ = v___x_7529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7534_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7534_, 0, v_a_7527_);
                    v___x_7532_ = v_reuseFailAlloc_7534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7533_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7533_, 0, v___x_7532_);
                return v___x_7533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_hasInterest___lam__0___boxed(
    mut v___y_7537_: *mut LeanObject,
    mut v_x_7538_: *mut LeanObject,
    mut v___y_7539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7540_: *mut LeanObject = core::ptr::null_mut();
    v_res_7540_ = l_Std_Http_Body_Stream_hasInterest___lam__0(v___y_7537_, v_x_7538_);
    lean_dec(v___y_7537_);
    return v_res_7540_;
}
pub unsafe fn l_Std_Http_Body_Stream_hasInterest___lam__1(
    mut v___y_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: u8 = 0;
    let mut v___x_7547_: *mut LeanObject = core::ptr::null_mut();
    v___x_7543_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_7541_);
    lean_inc(v___y_7541_);
    v___f_7544_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_hasInterest___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7544_, 0, v___y_7541_);
    v___x_7545_ = lean_unsigned_to_nat(0);
    v___x_7546_ = 0;
    v___x_7547_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7545_,
        v___x_7546_,
        v___x_7543_,
        v___f_7544_,
    );
    return v___x_7547_;
}
pub unsafe fn l_Std_Http_Body_Stream_hasInterest___lam__1___boxed(
    mut v___y_7548_: *mut LeanObject,
    mut v___y_7549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7550_: *mut LeanObject = core::ptr::null_mut();
    v_res_7550_ = l_Std_Http_Body_Stream_hasInterest___lam__1(v___y_7548_);
    lean_dec(v___y_7548_);
    return v_res_7550_;
}
pub unsafe fn l_Std_Http_Body_Stream_hasInterest(
    mut v_stream_7552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    v___f_7554_ = l_Std_Http_Body_Stream_hasInterest___closed__0;
    v___x_7555_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_stream_7552_,
        v___f_7554_,
    );
    return v___x_7555_;
}
pub unsafe fn l_Std_Http_Body_Stream_hasInterest___boxed(
    mut v_stream_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7558_: *mut LeanObject = core::ptr::null_mut();
    v_res_7558_ = l_Std_Http_Body_Stream_hasInterest(v_stream_7556_);
    return v_res_7558_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(
    mut v_lose_7559_: *mut LeanObject,
    mut v___y_7560_: *mut LeanObject,
    mut v___x_7561_: u8,
    mut v_promise_7562_: *mut LeanObject,
    mut v_x_7563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7568_: u8 = 0;
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7573_: u8 = 0;
    let mut v_a_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7577_: u8 = 0;
    let mut v___x_7578_: u8 = 0;
    let mut v___x_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7563_) == 0 {
                    lean_dec_ref(v_lose_7559_);
                    v_a_7565_ = lean_ctor_get(v_x_7563_, 0);
                    v_isSharedCheck_7573_ = (!lean_is_exclusive(v_x_7563_)) as u8;
                    if v_isSharedCheck_7573_ == 0 {
                        v___x_7567_ = v_x_7563_;
                        v_isShared_7568_ = v_isSharedCheck_7573_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7565_);
                        lean_dec(v_x_7563_);
                        v___x_7567_ = lean_box(0);
                        v_isShared_7568_ = v_isSharedCheck_7573_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7574_ = lean_ctor_get(v_x_7563_, 0);
                    v_isSharedCheck_7587_ = (!lean_is_exclusive(v_x_7563_)) as u8;
                    if v_isSharedCheck_7587_ == 0 {
                        v___x_7576_ = v_x_7563_;
                        v_isShared_7577_ = v_isSharedCheck_7587_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7574_);
                        lean_dec(v_x_7563_);
                        v___x_7576_ = lean_box(0);
                        v_isShared_7577_ = v_isSharedCheck_7587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7568_ == 0 {
                    v___x_7570_ = v___x_7567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7572_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7572_, 0, v_a_7565_);
                    v___x_7570_ = v_reuseFailAlloc_7572_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7571_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7571_, 0, v___x_7570_);
                return v___x_7571_;
            }
            3 => {
                v___x_7578_ = (lean_unbox(v_a_7574_) as u8);
                lean_dec(v_a_7574_);
                if v___x_7578_ == 0 {
                    lean_del_object(v___x_7576_);
                    lean_inc(v___y_7560_);
                    v___x_7579_ = lean_apply_2(v_lose_7559_, v___y_7560_, lean_box(0));
                    return v___x_7579_;
                } else {
                    lean_dec_ref(v_lose_7559_);
                    v___x_7580_ = lean_box((v___x_7561_) as usize);
                    if v_isShared_7577_ == 0 {
                        lean_ctor_set(v___x_7576_, 0, v___x_7580_);
                        v___x_7582_ = v___x_7576_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7586_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7586_, 0, v___x_7580_);
                        v___x_7582_ = v_reuseFailAlloc_7586_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7583_ = lean_io_promise_resolve(v___x_7582_, v_promise_7562_);
                v___x_7584_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7584_, 0, v___x_7583_);
                v___x_7585_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7585_, 0, v___x_7584_);
                return v___x_7585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed(
    mut v_lose_7588_: *mut LeanObject,
    mut v___y_7589_: *mut LeanObject,
    mut v___x_7590_: *mut LeanObject,
    mut v_promise_7591_: *mut LeanObject,
    mut v_x_7592_: *mut LeanObject,
    mut v___y_7593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4623__boxed_7594_: u8 = 0;
    let mut v_res_7595_: *mut LeanObject = core::ptr::null_mut();
    v___x_4623__boxed_7594_ = (lean_unbox(v___x_7590_) as u8);
    v_res_7595_ =
        l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0(
            v_lose_7588_,
            v___y_7589_,
            v___x_4623__boxed_7594_,
            v_promise_7591_,
            v_x_7592_,
        );
    lean_dec(v_promise_7591_);
    lean_dec(v___y_7589_);
    return v_res_7595_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(
    mut v_w_7596_: *mut LeanObject,
    mut v_lose_7597_: *mut LeanObject,
    mut v___y_7598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_7601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: u8 = 0;
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7607_: u8 = 0;
    let mut v___x_7608_: u8 = 0;
    let mut v___x_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: u8 = 0;
    let mut v___x_7617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_7600_ = lean_ctor_get(v_w_7596_, 0);
                lean_inc(v_finished_7600_);
                v_promise_7601_ = lean_ctor_get(v_w_7596_, 1);
                lean_inc(v_promise_7601_);
                lean_dec_ref(v_w_7596_);
                v___x_7602_ = lean_st_ref_take(v_finished_7600_);
                v___x_7603_ = 0;
                v___x_7604_ = lean_box((v___x_7603_) as usize);
                lean_inc(v___y_7598_);
                v___f_7605_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed as *mut core::ffi::c_void, 6, 4);
                lean_closure_set(v___f_7605_, 0, v_lose_7597_);
                lean_closure_set(v___f_7605_, 1, v___y_7598_);
                lean_closure_set(v___f_7605_, 2, v___x_7604_);
                lean_closure_set(v___f_7605_, 3, v_promise_7601_);
                v___x_7616_ = (lean_unbox(v___x_7602_) as u8);
                lean_dec(v___x_7602_);
                if v___x_7616_ == 0 {
                    v___x_7617_ = 1;
                    v___y_7607_ = v___x_7617_;
                    state = 1;
                    continue;
                } else {
                    v___y_7607_ = v___x_7603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7608_ = 1;
                v___x_7609_ = lean_box((v___x_7608_) as usize);
                v___x_7610_ = lean_st_ref_set(v_finished_7600_, v___x_7609_);
                lean_dec(v_finished_7600_);
                v___x_7611_ = lean_box((v___y_7607_) as usize);
                v___x_7612_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7612_, 0, v___x_7611_);
                v___x_7613_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7613_, 0, v___x_7612_);
                v___x_7614_ = lean_unsigned_to_nat(0);
                v___x_7615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7614_,
                    v___x_7603_,
                    v___x_7613_,
                    v___f_7605_,
                );
                return v___x_7615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___boxed(
    mut v_w_7618_: *mut LeanObject,
    mut v_lose_7619_: *mut LeanObject,
    mut v___y_7620_: *mut LeanObject,
    mut v___y_7621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7622_: *mut LeanObject = core::ptr::null_mut();
    v_res_7622_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(
        v_w_7618_,
        v_lose_7619_,
        v___y_7620_,
    );
    lean_dec(v___y_7620_);
    return v_res_7622_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(
    mut v_w_7623_: *mut LeanObject,
    mut v_lose_7624_: *mut LeanObject,
    mut v___y_7625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_7627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: u8 = 0;
    let mut v___x_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7634_: u8 = 0;
    let mut v___x_7635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: u8 = 0;
    let mut v___x_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: u8 = 0;
    let mut v___x_7644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_7627_ = lean_ctor_get(v_w_7623_, 0);
                lean_inc(v_finished_7627_);
                v_promise_7628_ = lean_ctor_get(v_w_7623_, 1);
                lean_inc(v_promise_7628_);
                lean_dec_ref(v_w_7623_);
                v___x_7629_ = lean_st_ref_take(v_finished_7627_);
                v___x_7630_ = 1;
                v___x_7631_ = lean_box((v___x_7630_) as usize);
                lean_inc(v___y_7625_);
                v___f_7632_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0___lam__0___boxed as *mut core::ffi::c_void, 6, 4);
                lean_closure_set(v___f_7632_, 0, v_lose_7624_);
                lean_closure_set(v___f_7632_, 1, v___y_7625_);
                lean_closure_set(v___f_7632_, 2, v___x_7631_);
                lean_closure_set(v___f_7632_, 3, v_promise_7628_);
                v___x_7643_ = (lean_unbox(v___x_7629_) as u8);
                lean_dec(v___x_7629_);
                if v___x_7643_ == 0 {
                    v___y_7634_ = v___x_7630_;
                    state = 1;
                    continue;
                } else {
                    v___x_7644_ = 0;
                    v___y_7634_ = v___x_7644_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7635_ = lean_box((v___x_7630_) as usize);
                v___x_7636_ = lean_st_ref_set(v_finished_7627_, v___x_7635_);
                lean_dec(v_finished_7627_);
                v___x_7637_ = lean_box((v___y_7634_) as usize);
                v___x_7638_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7638_, 0, v___x_7637_);
                v___x_7639_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7639_, 0, v___x_7638_);
                v___x_7640_ = lean_unsigned_to_nat(0);
                v___x_7641_ = 0;
                v___x_7642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7640_,
                    v___x_7641_,
                    v___x_7639_,
                    v___f_7632_,
                );
                return v___x_7642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1___boxed(
    mut v_w_7645_: *mut LeanObject,
    mut v_lose_7646_: *mut LeanObject,
    mut v___y_7647_: *mut LeanObject,
    mut v___y_7648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7649_: *mut LeanObject = core::ptr::null_mut();
    v_res_7649_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(
        v_w_7645_,
        v_lose_7646_,
        v___y_7647_,
    );
    lean_dec(v___y_7647_);
    return v_res_7649_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__0(
    mut v_x_7666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7671_: u8 = 0;
    let mut v___x_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7676_: u8 = 0;
    let mut v_a_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7679_: u8 = 0;
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7666_) == 0 {
                    v_a_7668_ = lean_ctor_get(v_x_7666_, 0);
                    v_isSharedCheck_7676_ = (!lean_is_exclusive(v_x_7666_)) as u8;
                    if v_isSharedCheck_7676_ == 0 {
                        v___x_7670_ = v_x_7666_;
                        v_isShared_7671_ = v_isSharedCheck_7676_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7668_);
                        lean_dec(v_x_7666_);
                        v___x_7670_ = lean_box(0);
                        v_isShared_7671_ = v_isSharedCheck_7676_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7677_ = lean_ctor_get(v_x_7666_, 0);
                    lean_inc(v_a_7677_);
                    lean_dec_ref_known(v_x_7666_, 1);
                    v_pendingConsumer_7678_ = lean_ctor_get(v_a_7677_, 1);
                    if lean_obj_tag(v_pendingConsumer_7678_) == 0 {
                        v_closed_7679_ = lean_ctor_get_uint8(
                            v_a_7677_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        );
                        lean_dec(v_a_7677_);
                        if v_closed_7679_ == 0 {
                            v___x_7680_ =
                                l_Std_Http_Body_Stream_interestSelector___lam__0___closed__0;
                            return v___x_7680_;
                        } else {
                            v___x_7681_ =
                                l_Std_Http_Body_Stream_interestSelector___lam__0___closed__3;
                            return v___x_7681_;
                        }
                    } else {
                        lean_dec(v_a_7677_);
                        v___x_7682_ = l_Std_Http_Body_Stream_interestSelector___lam__0___closed__6;
                        return v___x_7682_;
                    }
                }
            }
            1 => {
                if v_isShared_7671_ == 0 {
                    v___x_7673_ = v___x_7670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7675_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7675_, 0, v_a_7668_);
                    v___x_7673_ = v_reuseFailAlloc_7675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7674_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7674_, 0, v___x_7673_);
                return v___x_7674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__0___boxed(
    mut v_x_7683_: *mut LeanObject,
    mut v___y_7684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7685_: *mut LeanObject = core::ptr::null_mut();
    v_res_7685_ = l_Std_Http_Body_Stream_interestSelector___lam__0(v_x_7683_);
    return v_res_7685_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__3(
    mut v_waiter_7693_: *mut LeanObject,
    mut v___y_7694_: *mut LeanObject,
    mut v_x_7695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7700_: u8 = 0;
    let mut v___x_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7705_: u8 = 0;
    let mut v_a_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7709_: u8 = 0;
    let mut v_pendingConsumer_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7711_: u8 = 0;
    let mut v_interestWaiter_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_knownSize_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingIncompleteChunk_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7718_: u8 = 0;
    let mut v___x_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7728_: u8 = 0;
    let mut v_unused_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7695_) == 0 {
                    lean_dec_ref(v_waiter_7693_);
                    v_a_7697_ = lean_ctor_get(v_x_7695_, 0);
                    v_isSharedCheck_7705_ = (!lean_is_exclusive(v_x_7695_)) as u8;
                    if v_isSharedCheck_7705_ == 0 {
                        v___x_7699_ = v_x_7695_;
                        v_isShared_7700_ = v_isSharedCheck_7705_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7697_);
                        lean_dec(v_x_7695_);
                        v___x_7699_ = lean_box(0);
                        v_isShared_7700_ = v_isSharedCheck_7705_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7706_ = lean_ctor_get(v_x_7695_, 0);
                    v_isSharedCheck_7736_ = (!lean_is_exclusive(v_x_7695_)) as u8;
                    if v_isSharedCheck_7736_ == 0 {
                        v___x_7708_ = v_x_7695_;
                        v_isShared_7709_ = v_isSharedCheck_7736_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7706_);
                        lean_dec(v_x_7695_);
                        v___x_7708_ = lean_box(0);
                        v_isShared_7709_ = v_isSharedCheck_7736_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7700_ == 0 {
                    v___x_7702_ = v___x_7699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7704_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7704_, 0, v_a_7697_);
                    v___x_7702_ = v_reuseFailAlloc_7704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7703_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7703_, 0, v___x_7702_);
                return v___x_7703_;
            }
            3 => {
                v_pendingConsumer_7710_ = lean_ctor_get(v_a_7706_, 1);
                lean_inc(v_pendingConsumer_7710_);
                if lean_obj_tag(v_pendingConsumer_7710_) == 0 {
                    v_closed_7711_ = lean_ctor_get_uint8(
                        v_a_7706_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    if v_closed_7711_ == 0 {
                        v_interestWaiter_7712_ = lean_ctor_get(v_a_7706_, 2);
                        if lean_obj_tag(v_interestWaiter_7712_) == 0 {
                            v_pendingProducer_7713_ = lean_ctor_get(v_a_7706_, 0);
                            v_knownSize_7714_ = lean_ctor_get(v_a_7706_, 3);
                            v_pendingIncompleteChunk_7715_ = lean_ctor_get(v_a_7706_, 4);
                            v_isSharedCheck_7728_ = (!lean_is_exclusive(v_a_7706_)) as u8;
                            if v_isSharedCheck_7728_ == 0 {
                                v_unused_7729_ = lean_ctor_get(v_a_7706_, 2);
                                lean_dec(v_unused_7729_);
                                v_unused_7730_ = lean_ctor_get(v_a_7706_, 1);
                                lean_dec(v_unused_7730_);
                                v___x_7717_ = v_a_7706_;
                                v_isShared_7718_ = v_isSharedCheck_7728_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_pendingIncompleteChunk_7715_);
                                lean_inc(v_knownSize_7714_);
                                lean_inc(v_pendingProducer_7713_);
                                lean_dec(v_a_7706_);
                                v___x_7717_ = lean_box(0);
                                v_isShared_7718_ = v_isSharedCheck_7728_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7708_);
                            lean_dec(v_a_7706_);
                            lean_dec_ref(v_waiter_7693_);
                            v___x_7731_ =
                                l_Std_Http_Body_Stream_interestSelector___lam__3___closed__3;
                            return v___x_7731_;
                        }
                    } else {
                        lean_del_object(v___x_7708_);
                        lean_dec(v_a_7706_);
                        v___f_7732_ = l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0;
                        v___x_7733_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__0(v_waiter_7693_, v___f_7732_, v___y_7694_);
                        return v___x_7733_;
                    }
                } else {
                    lean_dec_ref_known(v_pendingConsumer_7710_, 1);
                    lean_del_object(v___x_7708_);
                    lean_dec(v_a_7706_);
                    v___f_7734_ = l_Std_Http_Body_Stream_recvSelector___lam__4___closed__0;
                    v___x_7735_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Stream_interestSelector_spec__1(v_waiter_7693_, v___f_7734_, v___y_7694_);
                    return v___x_7735_;
                }
            }
            4 => {
                v___x_7719_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7719_, 0, v_waiter_7693_);
                if v_isShared_7718_ == 0 {
                    lean_ctor_set(v___x_7717_, 2, v___x_7719_);
                    v___x_7721_ = v___x_7717_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7727_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7727_, 0, v_pendingProducer_7713_);
                    lean_ctor_set(v_reuseFailAlloc_7727_, 1, v_pendingConsumer_7710_);
                    lean_ctor_set(v_reuseFailAlloc_7727_, 2, v___x_7719_);
                    lean_ctor_set(v_reuseFailAlloc_7727_, 3, v_knownSize_7714_);
                    lean_ctor_set(v_reuseFailAlloc_7727_, 4, v_pendingIncompleteChunk_7715_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7727_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_7711_,
                    );
                    v___x_7721_ = v_reuseFailAlloc_7727_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7722_ = lean_st_ref_set(v___y_7694_, v___x_7721_);
                if v_isShared_7709_ == 0 {
                    lean_ctor_set(v___x_7708_, 0, v___x_7722_);
                    v___x_7724_ = v___x_7708_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7726_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7726_, 0, v___x_7722_);
                    v___x_7724_ = v_reuseFailAlloc_7726_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7725_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7725_, 0, v___x_7724_);
                return v___x_7725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__3___boxed(
    mut v_waiter_7737_: *mut LeanObject,
    mut v___y_7738_: *mut LeanObject,
    mut v_x_7739_: *mut LeanObject,
    mut v___y_7740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7741_: *mut LeanObject = core::ptr::null_mut();
    v_res_7741_ =
        l_Std_Http_Body_Stream_interestSelector___lam__3(v_waiter_7737_, v___y_7738_, v_x_7739_);
    lean_dec(v___y_7738_);
    return v_res_7741_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__1(
    mut v___y_7742_: *mut LeanObject,
    mut v___f_7743_: *mut LeanObject,
    mut v_x_7744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7749_: u8 = 0;
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: u8 = 0;
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7758_: u8 = 0;
    let mut v_unused_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7744_) == 0 {
                    lean_dec_ref(v___f_7743_);
                    v___x_7746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7746_, 0, v_x_7744_);
                    return v___x_7746_;
                } else {
                    v_isSharedCheck_7758_ = (!lean_is_exclusive(v_x_7744_)) as u8;
                    if v_isSharedCheck_7758_ == 0 {
                        v_unused_7759_ = lean_ctor_get(v_x_7744_, 0);
                        lean_dec(v_unused_7759_);
                        v___x_7748_ = v_x_7744_;
                        v_isShared_7749_ = v_isSharedCheck_7758_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_7744_);
                        v___x_7748_ = lean_box(0);
                        v_isShared_7749_ = v_isSharedCheck_7758_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7750_ = lean_st_ref_get(v___y_7742_);
                if v_isShared_7749_ == 0 {
                    lean_ctor_set(v___x_7748_, 0, v___x_7750_);
                    v___x_7752_ = v___x_7748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7757_, 0, v___x_7750_);
                    v___x_7752_ = v_reuseFailAlloc_7757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7753_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7753_, 0, v___x_7752_);
                v___x_7754_ = lean_unsigned_to_nat(0);
                v___x_7755_ = 0;
                v___x_7756_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7754_,
                    v___x_7755_,
                    v___x_7753_,
                    v___f_7743_,
                );
                return v___x_7756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__1___boxed(
    mut v___y_7760_: *mut LeanObject,
    mut v___f_7761_: *mut LeanObject,
    mut v_x_7762_: *mut LeanObject,
    mut v___y_7763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7764_: *mut LeanObject = core::ptr::null_mut();
    v_res_7764_ =
        l_Std_Http_Body_Stream_interestSelector___lam__1(v___y_7760_, v___f_7761_, v_x_7762_);
    lean_dec(v___y_7760_);
    return v_res_7764_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__2(
    mut v_waiter_7765_: *mut LeanObject,
    mut v___y_7766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: u8 = 0;
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    v___x_7768_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_7766_);
    lean_inc_n(v___y_7766_, 2);
    v___f_7769_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_interestSelector___lam__3___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7769_, 0, v_waiter_7765_);
    lean_closure_set(v___f_7769_, 1, v___y_7766_);
    v___f_7770_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_interestSelector___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7770_, 0, v___y_7766_);
    lean_closure_set(v___f_7770_, 1, v___f_7769_);
    v___x_7771_ = lean_unsigned_to_nat(0);
    v___x_7772_ = 0;
    v___x_7773_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7771_,
        v___x_7772_,
        v___x_7768_,
        v___f_7770_,
    );
    return v___x_7773_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__2___boxed(
    mut v_waiter_7774_: *mut LeanObject,
    mut v___y_7775_: *mut LeanObject,
    mut v___y_7776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7777_: *mut LeanObject = core::ptr::null_mut();
    v_res_7777_ = l_Std_Http_Body_Stream_interestSelector___lam__2(v_waiter_7774_, v___y_7775_);
    lean_dec(v___y_7775_);
    return v_res_7777_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__4(
    mut v_stream_7778_: *mut LeanObject,
    mut v_waiter_7779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    v___f_7781_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_interestSelector___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7781_, 0, v_waiter_7779_);
    v___x_7782_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_stream_7778_,
        v___f_7781_,
    );
    return v___x_7782_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__4___boxed(
    mut v_stream_7783_: *mut LeanObject,
    mut v_waiter_7784_: *mut LeanObject,
    mut v___y_7785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7786_: *mut LeanObject = core::ptr::null_mut();
    v_res_7786_ = l_Std_Http_Body_Stream_interestSelector___lam__4(v_stream_7783_, v_waiter_7784_);
    return v_res_7786_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__5(
    mut v___y_7787_: *mut LeanObject,
    mut v___f_7788_: *mut LeanObject,
    mut v_x_7789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7794_: u8 = 0;
    let mut v___x_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7799_: u8 = 0;
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7802_: u8 = 0;
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: u8 = 0;
    let mut v___x_7809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7811_: u8 = 0;
    let mut v_unused_7812_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7789_) == 0 {
                    lean_dec_ref(v___f_7788_);
                    v_a_7791_ = lean_ctor_get(v_x_7789_, 0);
                    v_isSharedCheck_7799_ = (!lean_is_exclusive(v_x_7789_)) as u8;
                    if v_isSharedCheck_7799_ == 0 {
                        v___x_7793_ = v_x_7789_;
                        v_isShared_7794_ = v_isSharedCheck_7799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7791_);
                        lean_dec(v_x_7789_);
                        v___x_7793_ = lean_box(0);
                        v_isShared_7794_ = v_isSharedCheck_7799_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_7811_ = (!lean_is_exclusive(v_x_7789_)) as u8;
                    if v_isSharedCheck_7811_ == 0 {
                        v_unused_7812_ = lean_ctor_get(v_x_7789_, 0);
                        lean_dec(v_unused_7812_);
                        v___x_7801_ = v_x_7789_;
                        v_isShared_7802_ = v_isSharedCheck_7811_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_7789_);
                        v___x_7801_ = lean_box(0);
                        v_isShared_7802_ = v_isSharedCheck_7811_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7794_ == 0 {
                    v___x_7796_ = v___x_7793_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7798_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7798_, 0, v_a_7791_);
                    v___x_7796_ = v_reuseFailAlloc_7798_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7797_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7797_, 0, v___x_7796_);
                return v___x_7797_;
            }
            3 => {
                v___x_7803_ = lean_st_ref_get(v___y_7787_);
                if v_isShared_7802_ == 0 {
                    lean_ctor_set(v___x_7801_, 0, v___x_7803_);
                    v___x_7805_ = v___x_7801_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7810_, 0, v___x_7803_);
                    v___x_7805_ = v_reuseFailAlloc_7810_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7806_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7806_, 0, v___x_7805_);
                v___x_7807_ = lean_unsigned_to_nat(0);
                v___x_7808_ = 0;
                v___x_7809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7807_,
                    v___x_7808_,
                    v___x_7806_,
                    v___f_7788_,
                );
                return v___x_7809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__5___boxed(
    mut v___y_7813_: *mut LeanObject,
    mut v___f_7814_: *mut LeanObject,
    mut v_x_7815_: *mut LeanObject,
    mut v___y_7816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7817_: *mut LeanObject = core::ptr::null_mut();
    v_res_7817_ =
        l_Std_Http_Body_Stream_interestSelector___lam__5(v___y_7813_, v___f_7814_, v_x_7815_);
    lean_dec(v___y_7813_);
    return v_res_7817_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__6(
    mut v___f_7818_: *mut LeanObject,
    mut v___y_7819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: u8 = 0;
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    v___x_7821_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_pruneFinishedWaiters___at___00Std_Http_Body_Stream_tryRecv_spec__1(v___y_7819_);
    lean_inc(v___y_7819_);
    v___f_7822_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_interestSelector___lam__5___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7822_, 0, v___y_7819_);
    lean_closure_set(v___f_7822_, 1, v___f_7818_);
    v___x_7823_ = lean_unsigned_to_nat(0);
    v___x_7824_ = 0;
    v___x_7825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7823_,
        v___x_7824_,
        v___x_7821_,
        v___f_7822_,
    );
    return v___x_7825_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector___lam__6___boxed(
    mut v___f_7826_: *mut LeanObject,
    mut v___y_7827_: *mut LeanObject,
    mut v___y_7828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7829_: *mut LeanObject = core::ptr::null_mut();
    v_res_7829_ = l_Std_Http_Body_Stream_interestSelector___lam__6(v___f_7826_, v___y_7827_);
    lean_dec(v___y_7827_);
    return v_res_7829_;
}
pub unsafe fn l_Std_Http_Body_Stream_interestSelector(
    mut v_stream_7833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    v___f_7834_ = l_Std_Http_Body_Stream_recvSelector___closed__0;
    lean_inc_ref_n(v_stream_7833_, 2);
    v___f_7835_ = lean_alloc_closure(
        l_Std_Http_Body_Stream_interestSelector___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7835_, 0, v_stream_7833_);
    v___f_7836_ = l_Std_Http_Body_Stream_interestSelector___closed__1;
    v___x_7837_ = lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_7837_, 0, lean_box(0));
    lean_closure_set(v___x_7837_, 1, lean_box(0));
    lean_closure_set(v___x_7837_, 2, v_stream_7833_);
    lean_closure_set(v___x_7837_, 3, v___f_7836_);
    v___x_7838_ = lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_7838_, 0, lean_box(0));
    lean_closure_set(v___x_7838_, 1, lean_box(0));
    lean_closure_set(v___x_7838_, 2, v_stream_7833_);
    lean_closure_set(v___x_7838_, 3, v___f_7834_);
    v___x_7839_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7839_, 0, v___x_7837_);
    lean_ctor_set(v___x_7839_, 1, v___f_7835_);
    lean_ctor_set(v___x_7839_, 2, v___x_7838_);
    return v___x_7839_;
}
pub unsafe fn l_Std_Http_Body_stream___lam__0(mut v___y_7840_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7844_: u8 = 0;
    let mut v___x_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7848_: u8 = 0;
    let mut v_a_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7852_: u8 = 0;
    let mut v_fst_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_7840_) == 0 {
                    v_a_7841_ = lean_ctor_get(v___y_7840_, 0);
                    v_isSharedCheck_7848_ = (!lean_is_exclusive(v___y_7840_)) as u8;
                    if v_isSharedCheck_7848_ == 0 {
                        v___x_7843_ = v___y_7840_;
                        v_isShared_7844_ = v_isSharedCheck_7848_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7841_);
                        lean_dec(v___y_7840_);
                        v___x_7843_ = lean_box(0);
                        v_isShared_7844_ = v_isSharedCheck_7848_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7849_ = lean_ctor_get(v___y_7840_, 0);
                    v_isSharedCheck_7857_ = (!lean_is_exclusive(v___y_7840_)) as u8;
                    if v_isSharedCheck_7857_ == 0 {
                        v___x_7851_ = v___y_7840_;
                        v_isShared_7852_ = v_isSharedCheck_7857_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7849_);
                        lean_dec(v___y_7840_);
                        v___x_7851_ = lean_box(0);
                        v_isShared_7852_ = v_isSharedCheck_7857_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7844_ == 0 {
                    v___x_7846_ = v___x_7843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7847_, 0, v_a_7841_);
                    v___x_7846_ = v_reuseFailAlloc_7847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7846_;
            }
            3 => {
                v_fst_7853_ = lean_ctor_get(v_a_7849_, 0);
                lean_inc(v_fst_7853_);
                lean_dec(v_a_7849_);
                if v_isShared_7852_ == 0 {
                    lean_ctor_set(v___x_7851_, 0, v_fst_7853_);
                    v___x_7855_ = v___x_7851_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7856_, 0, v_fst_7853_);
                    v___x_7855_ = v_reuseFailAlloc_7856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_stream___lam__1(
    mut v_a_7858_: *mut LeanObject,
    mut v_x_7859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    v___x_7861_ = l_Std_Http_Body_Stream_close(v_a_7858_);
    return v___x_7861_;
}
pub unsafe fn l_Std_Http_Body_stream___lam__1___boxed(
    mut v_a_7862_: *mut LeanObject,
    mut v_x_7863_: *mut LeanObject,
    mut v___y_7864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7865_: *mut LeanObject = core::ptr::null_mut();
    v_res_7865_ = l_Std_Http_Body_stream___lam__1(v_a_7862_, v_x_7863_);
    lean_dec(v_x_7863_);
    return v_res_7865_;
}
pub unsafe fn l_Std_Http_Body_stream___lam__2(
    mut v___x_7866_: *mut LeanObject,
    mut v___f_7867_: *mut LeanObject,
    mut v___x_7868_: *mut LeanObject,
    mut v___f_7869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7871_: u8 = 0;
    let mut v___x_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7880_: u8 = 0;
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7884_: u8 = 0;
    let mut v_a_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7888_: u8 = 0;
    let mut v_fst_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7893_: u8 = 0;
    let mut v_a_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7897_: u8 = 0;
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7871_ = 0;
                lean_inc(v___x_7868_);
                v___x_7872_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___x_7866_,
                    v___f_7867_,
                    v___x_7868_,
                    v___x_7871_,
                );
                if lean_obj_tag(v___x_7872_) == 0 {
                    lean_dec_ref(v___f_7869_);
                    lean_dec(v___x_7868_);
                    v_a_7876_ = lean_ctor_get(v___x_7872_, 0);
                    lean_inc(v_a_7876_);
                    lean_dec_ref_known(v___x_7872_, 1);
                    if lean_obj_tag(v_a_7876_) == 0 {
                        v_a_7877_ = lean_ctor_get(v_a_7876_, 0);
                        v_isSharedCheck_7884_ = (!lean_is_exclusive(v_a_7876_)) as u8;
                        if v_isSharedCheck_7884_ == 0 {
                            v___x_7879_ = v_a_7876_;
                            v_isShared_7880_ = v_isSharedCheck_7884_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_7877_);
                            lean_dec(v_a_7876_);
                            v___x_7879_ = lean_box(0);
                            v_isShared_7880_ = v_isSharedCheck_7884_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_7885_ = lean_ctor_get(v_a_7876_, 0);
                        v_isSharedCheck_7893_ = (!lean_is_exclusive(v_a_7876_)) as u8;
                        if v_isSharedCheck_7893_ == 0 {
                            v___x_7887_ = v_a_7876_;
                            v_isShared_7888_ = v_isSharedCheck_7893_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7885_);
                            lean_dec(v_a_7876_);
                            v___x_7887_ = lean_box(0);
                            v_isShared_7888_ = v_isSharedCheck_7893_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_7894_ = lean_ctor_get(v___x_7872_, 0);
                    v_isSharedCheck_7902_ = (!lean_is_exclusive(v___x_7872_)) as u8;
                    if v_isSharedCheck_7902_ == 0 {
                        v___x_7896_ = v___x_7872_;
                        v_isShared_7897_ = v_isSharedCheck_7902_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_7894_);
                        lean_dec(v___x_7872_);
                        v___x_7896_ = lean_box(0);
                        v_isShared_7897_ = v_isSharedCheck_7902_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7875_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7875_, 0, v___y_7874_);
                return v___x_7875_;
            }
            2 => {
                if v_isShared_7880_ == 0 {
                    v___x_7882_ = v___x_7879_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7883_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7883_, 0, v_a_7877_);
                    v___x_7882_ = v_reuseFailAlloc_7883_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_7874_ = v___x_7882_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_7889_ = lean_ctor_get(v_a_7885_, 0);
                lean_inc(v_fst_7889_);
                lean_dec(v_a_7885_);
                if v_isShared_7888_ == 0 {
                    lean_ctor_set(v___x_7887_, 0, v_fst_7889_);
                    v___x_7891_ = v___x_7887_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7892_, 0, v_fst_7889_);
                    v___x_7891_ = v_reuseFailAlloc_7892_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_7874_ = v___x_7891_;
                state = 1;
                continue;
            }
            6 => {
                v___x_7898_ = lean_task_map(v___f_7869_, v_a_7894_, v___x_7868_, v___x_7871_);
                if v_isShared_7897_ == 0 {
                    lean_ctor_set(v___x_7896_, 0, v___x_7898_);
                    v___x_7900_ = v___x_7896_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7901_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7901_, 0, v___x_7898_);
                    v___x_7900_ = v_reuseFailAlloc_7901_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_stream___lam__2___boxed(
    mut v___x_7903_: *mut LeanObject,
    mut v___f_7904_: *mut LeanObject,
    mut v___x_7905_: *mut LeanObject,
    mut v___f_7906_: *mut LeanObject,
    mut v___y_7907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7908_: *mut LeanObject = core::ptr::null_mut();
    v_res_7908_ =
        l_Std_Http_Body_stream___lam__2(v___x_7903_, v___f_7904_, v___x_7905_, v___f_7906_);
    return v_res_7908_;
}
pub unsafe fn l_Std_Http_Body_stream___lam__3(
    mut v_x_7909_: *mut LeanObject,
    mut v_x_7910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7915_: u8 = 0;
    let mut v___x_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7920_: u8 = 0;
    let mut v___x_7921_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7910_) == 0 {
                    lean_dec_ref(v_x_7909_);
                    v_a_7912_ = lean_ctor_get(v_x_7910_, 0);
                    v_isSharedCheck_7920_ = (!lean_is_exclusive(v_x_7910_)) as u8;
                    if v_isSharedCheck_7920_ == 0 {
                        v___x_7914_ = v_x_7910_;
                        v_isShared_7915_ = v_isSharedCheck_7920_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7912_);
                        lean_dec(v_x_7910_);
                        v___x_7914_ = lean_box(0);
                        v_isShared_7915_ = v_isSharedCheck_7920_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_7910_, 1);
                    v___x_7921_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7921_, 0, v_x_7909_);
                    return v___x_7921_;
                }
            }
            1 => {
                if v_isShared_7915_ == 0 {
                    v___x_7917_ = v___x_7914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7919_, 0, v_a_7912_);
                    v___x_7917_ = v_reuseFailAlloc_7919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7918_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7918_, 0, v___x_7917_);
                return v___x_7918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_stream___lam__3___boxed(
    mut v_x_7922_: *mut LeanObject,
    mut v_x_7923_: *mut LeanObject,
    mut v___y_7924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7925_: *mut LeanObject = core::ptr::null_mut();
    v_res_7925_ = l_Std_Http_Body_stream___lam__3(v_x_7922_, v_x_7923_);
    return v_res_7925_;
}
pub unsafe fn l_Std_Http_Body_stream___lam__4(
    mut v_gen_7926_: *mut LeanObject,
    mut v___f_7927_: *mut LeanObject,
    mut v_x_7928_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_7928_) == 0 {
        let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_7927_);
        lean_dec_ref(v_gen_7926_);
        v___x_7930_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7930_, 0, v_x_7928_);
        return v___x_7930_;
    } else {
        let mut v_a_7931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7936_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_7937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7939_: u8 = 0;
        let mut v___x_7940_: *mut LeanObject = core::ptr::null_mut();
        v_a_7931_ = lean_ctor_get(v_x_7928_, 0);
        lean_inc_n(v_a_7931_, 2);
        v___f_7932_ = lean_alloc_closure(
            l_Std_Http_Body_stream___lam__1___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7932_, 0, v_a_7931_);
        v___x_7933_ = lean_apply_1(v_gen_7926_, v_a_7931_);
        v___x_7934_ = lean_unsigned_to_nat(0);
        v___f_7935_ = lean_alloc_closure(
            l_Std_Http_Body_stream___lam__2___boxed as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_7935_, 0, v___x_7933_);
        lean_closure_set(v___f_7935_, 1, v___f_7932_);
        lean_closure_set(v___f_7935_, 2, v___x_7934_);
        lean_closure_set(v___f_7935_, 3, v___f_7927_);
        v___x_7936_ = lean_io_as_task(v___f_7935_, v___x_7934_);
        lean_dec_ref(v___x_7936_);
        v___f_7937_ = lean_alloc_closure(
            l_Std_Http_Body_stream___lam__3___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_7937_, 0, v_x_7928_);
        v___x_7938_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
        v___x_7939_ = 0;
        v___x_7940_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_7934_,
            v___x_7939_,
            v___x_7938_,
            v___f_7937_,
        );
        return v___x_7940_;
    }
}
pub unsafe fn l_Std_Http_Body_stream___lam__4___boxed(
    mut v_gen_7941_: *mut LeanObject,
    mut v___f_7942_: *mut LeanObject,
    mut v_x_7943_: *mut LeanObject,
    mut v___y_7944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7945_: *mut LeanObject = core::ptr::null_mut();
    v_res_7945_ = l_Std_Http_Body_stream___lam__4(v_gen_7941_, v___f_7942_, v_x_7943_);
    return v_res_7945_;
}
pub unsafe fn l_Std_Http_Body_stream(mut v_gen_7947_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7953_: u8 = 0;
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    v___x_7949_ = l_Std_Http_Body_mkStream();
    v___f_7950_ = l_Std_Http_Body_stream___closed__0;
    v___f_7951_ = lean_alloc_closure(
        l_Std_Http_Body_stream___lam__4___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7951_, 0, v_gen_7947_);
    lean_closure_set(v___f_7951_, 1, v___f_7950_);
    v___x_7952_ = lean_unsigned_to_nat(0);
    v___x_7953_ = 0;
    v___x_7954_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7952_,
        v___x_7953_,
        v___x_7949_,
        v___f_7951_,
    );
    return v___x_7954_;
}
pub unsafe fn l_Std_Http_Body_stream___boxed(
    mut v_gen_7955_: *mut LeanObject,
    mut v_a_7956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7957_: *mut LeanObject = core::ptr::null_mut();
    v_res_7957_ = l_Std_Http_Body_stream(v_gen_7955_);
    return v_res_7957_;
}
pub unsafe fn l_Std_Http_Body_fromBytes___lam__0(
    mut v___x_7958_: *mut LeanObject,
    mut v___y_7959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingProducer_7962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pendingConsumer_7963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_interestWaiter_7964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7965_: u8 = 0;
    let mut v_pendingIncompleteChunk_7966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7969_: u8 = 0;
    let mut v___x_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7975_: u8 = 0;
    let mut v_unused_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7961_ = lean_st_ref_take(v___y_7959_);
                v_pendingProducer_7962_ = lean_ctor_get(v___x_7961_, 0);
                v_pendingConsumer_7963_ = lean_ctor_get(v___x_7961_, 1);
                v_interestWaiter_7964_ = lean_ctor_get(v___x_7961_, 2);
                v_closed_7965_ = lean_ctor_get_uint8(
                    v___x_7961_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_pendingIncompleteChunk_7966_ = lean_ctor_get(v___x_7961_, 4);
                v_isSharedCheck_7975_ = (!lean_is_exclusive(v___x_7961_)) as u8;
                if v_isSharedCheck_7975_ == 0 {
                    v_unused_7976_ = lean_ctor_get(v___x_7961_, 3);
                    lean_dec(v_unused_7976_);
                    v___x_7968_ = v___x_7961_;
                    v_isShared_7969_ = v_isSharedCheck_7975_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pendingIncompleteChunk_7966_);
                    lean_inc(v_interestWaiter_7964_);
                    lean_inc(v_pendingConsumer_7963_);
                    lean_inc(v_pendingProducer_7962_);
                    lean_dec(v___x_7961_);
                    v___x_7968_ = lean_box(0);
                    v_isShared_7969_ = v_isSharedCheck_7975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7969_ == 0 {
                    lean_ctor_set(v___x_7968_, 3, v___x_7958_);
                    v___x_7971_ = v___x_7968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7974_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7974_, 0, v_pendingProducer_7962_);
                    lean_ctor_set(v_reuseFailAlloc_7974_, 1, v_pendingConsumer_7963_);
                    lean_ctor_set(v_reuseFailAlloc_7974_, 2, v_interestWaiter_7964_);
                    lean_ctor_set(v_reuseFailAlloc_7974_, 3, v___x_7958_);
                    lean_ctor_set(v_reuseFailAlloc_7974_, 4, v_pendingIncompleteChunk_7966_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7974_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_closed_7965_,
                    );
                    v___x_7971_ = v_reuseFailAlloc_7974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7972_ = lean_st_ref_set(v___y_7959_, v___x_7971_);
                v___x_7973_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
                return v___x_7973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_fromBytes___lam__0___boxed(
    mut v___x_7977_: *mut LeanObject,
    mut v___y_7978_: *mut LeanObject,
    mut v___y_7979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7980_: *mut LeanObject = core::ptr::null_mut();
    v_res_7980_ = l_Std_Http_Body_fromBytes___lam__0(v___x_7977_, v___y_7978_);
    lean_dec(v___y_7978_);
    return v_res_7980_;
}
pub unsafe fn l_Std_Http_Body_fromBytes___lam__1(
    mut v___x_7981_: *mut LeanObject,
    mut v_content_7982_: *mut LeanObject,
    mut v_s_7983_: *mut LeanObject,
    mut v_x_7984_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_7984_) == 0 {
        let mut v___x_7986_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_7983_);
        lean_dec_ref(v_content_7982_);
        v___x_7986_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_7986_, 0, v_x_7984_);
        return v___x_7986_;
    } else {
        let mut v___x_7987_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7988_: u8 = 0;
        lean_dec_ref_known(v_x_7984_, 1);
        v___x_7987_ = lean_unsigned_to_nat(0);
        v___x_7988_ = lean_nat_dec_lt(v___x_7987_, v___x_7981_);
        if v___x_7988_ == 0 {
            let mut v___x_7989_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_7983_);
            lean_dec_ref(v_content_7982_);
            v___x_7989_ = l___private_Std_Http_Data_Body_Stream_0__Std_Http_Body_Channel_tryRecv_x27___at___00Std_Http_Body_Stream_tryRecv_spec__0___lam__1___closed__1;
            return v___x_7989_;
        } else {
            let mut v___x_7990_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7991_: u8 = 0;
            let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
            v___x_7990_ = l_Std_Http_Chunk_ofByteArray(v_content_7982_);
            v___x_7991_ = 0;
            v___x_7992_ = l_Std_Http_Body_Stream_send(v_s_7983_, v___x_7990_, v___x_7991_);
            return v___x_7992_;
        }
    }
}
pub unsafe fn l_Std_Http_Body_fromBytes___lam__1___boxed(
    mut v___x_7993_: *mut LeanObject,
    mut v_content_7994_: *mut LeanObject,
    mut v_s_7995_: *mut LeanObject,
    mut v_x_7996_: *mut LeanObject,
    mut v___y_7997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7998_: *mut LeanObject = core::ptr::null_mut();
    v_res_7998_ =
        l_Std_Http_Body_fromBytes___lam__1(v___x_7993_, v_content_7994_, v_s_7995_, v_x_7996_);
    lean_dec(v___x_7993_);
    return v_res_7998_;
}
pub unsafe fn l_Std_Http_Body_fromBytes___lam__2(
    mut v_content_7999_: *mut LeanObject,
    mut v_s_8000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8009_: u8 = 0;
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    v___x_8002_ = lean_byte_array_size(v_content_7999_);
    v___x_8003_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8003_, 0, v___x_8002_);
    v___x_8004_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8004_, 0, v___x_8003_);
    v___f_8005_ = lean_alloc_closure(
        l_Std_Http_Body_fromBytes___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8005_, 0, v___x_8004_);
    lean_inc_ref(v_s_8000_);
    v___x_8006_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
        v_s_8000_,
        v___f_8005_,
    );
    v___f_8007_ = lean_alloc_closure(
        l_Std_Http_Body_fromBytes___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_8007_, 0, v___x_8002_);
    lean_closure_set(v___f_8007_, 1, v_content_7999_);
    lean_closure_set(v___f_8007_, 2, v_s_8000_);
    v___x_8008_ = lean_unsigned_to_nat(0);
    v___x_8009_ = 0;
    v___x_8010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8008_,
        v___x_8009_,
        v___x_8006_,
        v___f_8007_,
    );
    return v___x_8010_;
}
pub unsafe fn l_Std_Http_Body_fromBytes___lam__2___boxed(
    mut v_content_8011_: *mut LeanObject,
    mut v_s_8012_: *mut LeanObject,
    mut v___y_8013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8014_: *mut LeanObject = core::ptr::null_mut();
    v_res_8014_ = l_Std_Http_Body_fromBytes___lam__2(v_content_8011_, v_s_8012_);
    return v_res_8014_;
}
pub unsafe fn l_Std_Http_Body_fromBytes(mut v_content_8015_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut LeanObject = core::ptr::null_mut();
    v___f_8017_ = lean_alloc_closure(
        l_Std_Http_Body_fromBytes___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8017_, 0, v_content_8015_);
    v___x_8018_ = l_Std_Http_Body_stream(v___f_8017_);
    return v___x_8018_;
}
pub unsafe fn l_Std_Http_Body_fromBytes___boxed(
    mut v_content_8019_: *mut LeanObject,
    mut v_a_8020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8021_: *mut LeanObject = core::ptr::null_mut();
    v_res_8021_ = l_Std_Http_Body_fromBytes(v_content_8019_);
    return v_res_8021_;
}
pub unsafe fn l_Std_Http_Body_empty___lam__2(
    mut v_a_8022_: *mut LeanObject,
    mut v___f_8023_: *mut LeanObject,
    mut v_x_8024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8029_: u8 = 0;
    let mut v___x_8031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8034_: u8 = 0;
    let mut v___x_8035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: u8 = 0;
    let mut v___x_8038_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8024_) == 0 {
                    lean_dec_ref(v___f_8023_);
                    lean_dec_ref(v_a_8022_);
                    v_a_8026_ = lean_ctor_get(v_x_8024_, 0);
                    v_isSharedCheck_8034_ = (!lean_is_exclusive(v_x_8024_)) as u8;
                    if v_isSharedCheck_8034_ == 0 {
                        v___x_8028_ = v_x_8024_;
                        v_isShared_8029_ = v_isSharedCheck_8034_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8026_);
                        lean_dec(v_x_8024_);
                        v___x_8028_ = lean_box(0);
                        v_isShared_8029_ = v_isSharedCheck_8034_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_8024_, 1);
                    v___x_8035_ = l_Std_Http_Body_Stream_close(v_a_8022_);
                    v___x_8036_ = lean_unsigned_to_nat(0);
                    v___x_8037_ = 0;
                    v___x_8038_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_8036_,
                            v___x_8037_,
                            v___x_8035_,
                            v___f_8023_,
                        );
                    return v___x_8038_;
                }
            }
            1 => {
                if v_isShared_8029_ == 0 {
                    v___x_8031_ = v___x_8028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8033_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8033_, 0, v_a_8026_);
                    v___x_8031_ = v_reuseFailAlloc_8033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8032_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8032_, 0, v___x_8031_);
                return v___x_8032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_empty___lam__2___boxed(
    mut v_a_8039_: *mut LeanObject,
    mut v___f_8040_: *mut LeanObject,
    mut v_x_8041_: *mut LeanObject,
    mut v___y_8042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8043_: *mut LeanObject = core::ptr::null_mut();
    v_res_8043_ = l_Std_Http_Body_empty___lam__2(v_a_8039_, v___f_8040_, v_x_8041_);
    return v_res_8043_;
}
pub unsafe fn l_Std_Http_Body_empty___lam__0(mut v_x_8050_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_8050_) == 0 {
        let mut v___x_8052_: *mut LeanObject = core::ptr::null_mut();
        v___x_8052_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_8052_, 0, v_x_8050_);
        return v___x_8052_;
    } else {
        let mut v_a_8053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8059_: u8 = 0;
        let mut v___x_8060_: *mut LeanObject = core::ptr::null_mut();
        v_a_8053_ = lean_ctor_get(v_x_8050_, 0);
        lean_inc_n(v_a_8053_, 2);
        v___x_8054_ = lean_unsigned_to_nat(0);
        v___f_8055_ = l_Std_Http_Body_empty___lam__0___closed__2;
        v___x_8056_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Stream_tryRecv_spec__2___redArg(
            v_a_8053_,
            v___f_8055_,
        );
        v___f_8057_ = lean_alloc_closure(
            l_Std_Http_Body_stream___lam__3___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_8057_, 0, v_x_8050_);
        v___f_8058_ = lean_alloc_closure(
            l_Std_Http_Body_empty___lam__2___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_8058_, 0, v_a_8053_);
        lean_closure_set(v___f_8058_, 1, v___f_8057_);
        v___x_8059_ = 0;
        v___x_8060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_8054_,
            v___x_8059_,
            v___x_8056_,
            v___f_8058_,
        );
        return v___x_8060_;
    }
}
pub unsafe fn l_Std_Http_Body_empty___lam__0___boxed(
    mut v_x_8061_: *mut LeanObject,
    mut v___y_8062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8063_: *mut LeanObject = core::ptr::null_mut();
    v_res_8063_ = l_Std_Http_Body_empty___lam__0(v_x_8061_);
    return v_res_8063_;
}
pub unsafe fn l_Std_Http_Body_empty() -> *mut LeanObject {
    let mut v___x_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8069_: u8 = 0;
    let mut v___x_8070_: *mut LeanObject = core::ptr::null_mut();
    v___x_8066_ = l_Std_Http_Body_mkStream();
    v___f_8067_ = l_Std_Http_Body_empty___closed__0;
    v___x_8068_ = lean_unsigned_to_nat(0);
    v___x_8069_ = 0;
    v___x_8070_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8068_,
        v___x_8069_,
        v___x_8066_,
        v___f_8067_,
    );
    return v___x_8070_;
}
pub unsafe fn l_Std_Http_Body_empty___boxed(mut v_a_8071_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_8072_: *mut LeanObject = core::ptr::null_mut();
    v_res_8072_ = l_Std_Http_Body_empty();
    return v_res_8072_;
}
pub unsafe fn l_Std_Http_Body_instCoeResponseStreamAny___lam__0(
    mut v___x_8095_: *mut LeanObject,
    mut v_f_8096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_line_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8102_: u8 = 0;
    let mut v___x_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_8097_ = lean_ctor_get(v_f_8096_, 0);
                v_body_8098_ = lean_ctor_get(v_f_8096_, 1);
                v_extensions_8099_ = lean_ctor_get(v_f_8096_, 2);
                v_isSharedCheck_8107_ = (!lean_is_exclusive(v_f_8096_)) as u8;
                if v_isSharedCheck_8107_ == 0 {
                    v___x_8101_ = v_f_8096_;
                    v_isShared_8102_ = v_isSharedCheck_8107_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_extensions_8099_);
                    lean_inc(v_body_8098_);
                    lean_inc(v_line_8097_);
                    lean_dec(v_f_8096_);
                    v___x_8101_ = lean_box(0);
                    v_isShared_8102_ = v_isSharedCheck_8107_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8103_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_8095_, v_body_8098_);
                if v_isShared_8102_ == 0 {
                    lean_ctor_set(v___x_8101_, 1, v___x_8103_);
                    v___x_8105_ = v___x_8101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8106_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8106_, 0, v_line_8097_);
                    lean_ctor_set(v_reuseFailAlloc_8106_, 1, v___x_8103_);
                    lean_ctor_set(v_reuseFailAlloc_8106_, 2, v_extensions_8099_);
                    v___x_8105_ = v_reuseFailAlloc_8106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(
    mut v___x_8111_: *mut LeanObject,
    mut v_x_8112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8117_: u8 = 0;
    let mut v___x_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8122_: u8 = 0;
    let mut v_a_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8126_: u8 = 0;
    let mut v_line_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_8129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8132_: u8 = 0;
    let mut v___x_8133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8141_: u8 = 0;
    let mut v_isSharedCheck_8142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8112_) == 0 {
                    lean_dec_ref(v___x_8111_);
                    v_a_8114_ = lean_ctor_get(v_x_8112_, 0);
                    v_isSharedCheck_8122_ = (!lean_is_exclusive(v_x_8112_)) as u8;
                    if v_isSharedCheck_8122_ == 0 {
                        v___x_8116_ = v_x_8112_;
                        v_isShared_8117_ = v_isSharedCheck_8122_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8114_);
                        lean_dec(v_x_8112_);
                        v___x_8116_ = lean_box(0);
                        v_isShared_8117_ = v_isSharedCheck_8122_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8123_ = lean_ctor_get(v_x_8112_, 0);
                    v_isSharedCheck_8142_ = (!lean_is_exclusive(v_x_8112_)) as u8;
                    if v_isSharedCheck_8142_ == 0 {
                        v___x_8125_ = v_x_8112_;
                        v_isShared_8126_ = v_isSharedCheck_8142_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8123_);
                        lean_dec(v_x_8112_);
                        v___x_8125_ = lean_box(0);
                        v_isShared_8126_ = v_isSharedCheck_8142_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8117_ == 0 {
                    v___x_8119_ = v___x_8116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8121_, 0, v_a_8114_);
                    v___x_8119_ = v_reuseFailAlloc_8121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8120_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8120_, 0, v___x_8119_);
                return v___x_8120_;
            }
            3 => {
                v_line_8127_ = lean_ctor_get(v_a_8123_, 0);
                v_body_8128_ = lean_ctor_get(v_a_8123_, 1);
                v_extensions_8129_ = lean_ctor_get(v_a_8123_, 2);
                v_isSharedCheck_8141_ = (!lean_is_exclusive(v_a_8123_)) as u8;
                if v_isSharedCheck_8141_ == 0 {
                    v___x_8131_ = v_a_8123_;
                    v_isShared_8132_ = v_isSharedCheck_8141_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_extensions_8129_);
                    lean_inc(v_body_8128_);
                    lean_inc(v_line_8127_);
                    lean_dec(v_a_8123_);
                    v___x_8131_ = lean_box(0);
                    v_isShared_8132_ = v_isSharedCheck_8141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8133_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_8111_, v_body_8128_);
                if v_isShared_8132_ == 0 {
                    lean_ctor_set(v___x_8131_, 1, v___x_8133_);
                    v___x_8135_ = v___x_8131_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8140_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8140_, 0, v_line_8127_);
                    lean_ctor_set(v_reuseFailAlloc_8140_, 1, v___x_8133_);
                    lean_ctor_set(v_reuseFailAlloc_8140_, 2, v_extensions_8129_);
                    v___x_8135_ = v_reuseFailAlloc_8140_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_8126_ == 0 {
                    lean_ctor_set(v___x_8125_, 0, v___x_8135_);
                    v___x_8137_ = v___x_8125_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8139_, 0, v___x_8135_);
                    v___x_8137_ = v_reuseFailAlloc_8139_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_8138_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8138_, 0, v___x_8137_);
                return v___x_8138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0___boxed(
    mut v___x_8143_: *mut LeanObject,
    mut v_x_8144_: *mut LeanObject,
    mut v___y_8145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8146_: *mut LeanObject = core::ptr::null_mut();
    v_res_8146_ =
        l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__0(v___x_8143_, v_x_8144_);
    return v_res_8146_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(
    mut v___f_8147_: *mut LeanObject,
    mut v_action_8148_: *mut LeanObject,
    mut v___y_8149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8153_: u8 = 0;
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_8149_);
    v___x_8151_ = lean_apply_2(v_action_8148_, v___y_8149_, lean_box(0));
    v___x_8152_ = lean_unsigned_to_nat(0);
    v___x_8153_ = 0;
    v___x_8154_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8152_,
        v___x_8153_,
        v___x_8151_,
        v___f_8147_,
    );
    return v___x_8154_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1___boxed(
    mut v___f_8155_: *mut LeanObject,
    mut v_action_8156_: *mut LeanObject,
    mut v___y_8157_: *mut LeanObject,
    mut v___y_8158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8159_: *mut LeanObject = core::ptr::null_mut();
    v_res_8159_ = l_Std_Http_Body_instCoeContextAsyncResponseStreamAny___lam__1(
        v___f_8155_,
        v_action_8156_,
        v___y_8157_,
    );
    lean_dec_ref(v___y_8157_);
    return v_res_8159_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(
    mut v___f_8165_: *mut LeanObject,
    mut v_action_8166_: *mut LeanObject,
    mut v___y_8167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8171_: u8 = 0;
    let mut v___x_8172_: *mut LeanObject = core::ptr::null_mut();
    v___x_8169_ = lean_apply_1(v_action_8166_, lean_box(0));
    v___x_8170_ = lean_unsigned_to_nat(0);
    v___x_8171_ = 0;
    v___x_8172_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8170_,
        v___x_8171_,
        v___x_8169_,
        v___f_8165_,
    );
    return v___x_8172_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1___boxed(
    mut v___f_8173_: *mut LeanObject,
    mut v_action_8174_: *mut LeanObject,
    mut v___y_8175_: *mut LeanObject,
    mut v___y_8176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8177_: *mut LeanObject = core::ptr::null_mut();
    v_res_8177_ = l_Std_Http_Body_instCoeAsyncResponseStreamContextAsyncAny___lam__1(
        v___f_8173_,
        v_action_8174_,
        v___y_8175_,
    );
    lean_dec_ref(v___y_8175_);
    return v_res_8177_;
}
pub unsafe fn l_Std_Http_Request_Builder_stream___lam__0(
    mut v_builder_8181_: *mut LeanObject,
    mut v_x_8182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8187_: u8 = 0;
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8192_: u8 = 0;
    let mut v_a_8193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8196_: u8 = 0;
    let mut v___x_8197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8182_) == 0 {
                    v_a_8184_ = lean_ctor_get(v_x_8182_, 0);
                    v_isSharedCheck_8192_ = (!lean_is_exclusive(v_x_8182_)) as u8;
                    if v_isSharedCheck_8192_ == 0 {
                        v___x_8186_ = v_x_8182_;
                        v_isShared_8187_ = v_isSharedCheck_8192_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8184_);
                        lean_dec(v_x_8182_);
                        v___x_8186_ = lean_box(0);
                        v_isShared_8187_ = v_isSharedCheck_8192_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8193_ = lean_ctor_get(v_x_8182_, 0);
                    v_isSharedCheck_8202_ = (!lean_is_exclusive(v_x_8182_)) as u8;
                    if v_isSharedCheck_8202_ == 0 {
                        v___x_8195_ = v_x_8182_;
                        v_isShared_8196_ = v_isSharedCheck_8202_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8193_);
                        lean_dec(v_x_8182_);
                        v___x_8195_ = lean_box(0);
                        v_isShared_8196_ = v_isSharedCheck_8202_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8187_ == 0 {
                    v___x_8189_ = v___x_8186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8191_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8191_, 0, v_a_8184_);
                    v___x_8189_ = v_reuseFailAlloc_8191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8190_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8190_, 0, v___x_8189_);
                return v___x_8190_;
            }
            3 => {
                v___x_8197_ = l_Std_Http_Request_Builder_body___redArg(v_builder_8181_, v_a_8193_);
                if v_isShared_8196_ == 0 {
                    lean_ctor_set(v___x_8195_, 0, v___x_8197_);
                    v___x_8199_ = v___x_8195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8201_, 0, v___x_8197_);
                    v___x_8199_ = v_reuseFailAlloc_8201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8200_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8200_, 0, v___x_8199_);
                return v___x_8200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_stream___lam__0___boxed(
    mut v_builder_8203_: *mut LeanObject,
    mut v_x_8204_: *mut LeanObject,
    mut v___y_8205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8206_: *mut LeanObject = core::ptr::null_mut();
    v_res_8206_ = l_Std_Http_Request_Builder_stream___lam__0(v_builder_8203_, v_x_8204_);
    lean_dec_ref(v_builder_8203_);
    return v_res_8206_;
}
pub unsafe fn l_Std_Http_Request_Builder_stream(
    mut v_builder_8207_: *mut LeanObject,
    mut v_gen_8208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8213_: u8 = 0;
    let mut v___x_8214_: *mut LeanObject = core::ptr::null_mut();
    v___x_8210_ = l_Std_Http_Body_stream(v_gen_8208_);
    v___f_8211_ = lean_alloc_closure(
        l_Std_Http_Request_Builder_stream___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8211_, 0, v_builder_8207_);
    v___x_8212_ = lean_unsigned_to_nat(0);
    v___x_8213_ = 0;
    v___x_8214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8212_,
        v___x_8213_,
        v___x_8210_,
        v___f_8211_,
    );
    return v___x_8214_;
}
pub unsafe fn l_Std_Http_Request_Builder_stream___boxed(
    mut v_builder_8215_: *mut LeanObject,
    mut v_gen_8216_: *mut LeanObject,
    mut v_a_8217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8218_: *mut LeanObject = core::ptr::null_mut();
    v_res_8218_ = l_Std_Http_Request_Builder_stream(v_builder_8215_, v_gen_8216_);
    return v_res_8218_;
}
pub unsafe fn l_Std_Http_Response_Builder_stream___lam__0(
    mut v_builder_8219_: *mut LeanObject,
    mut v_x_8220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8225_: u8 = 0;
    let mut v___x_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8230_: u8 = 0;
    let mut v_a_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8234_: u8 = 0;
    let mut v___x_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8220_) == 0 {
                    v_a_8222_ = lean_ctor_get(v_x_8220_, 0);
                    v_isSharedCheck_8230_ = (!lean_is_exclusive(v_x_8220_)) as u8;
                    if v_isSharedCheck_8230_ == 0 {
                        v___x_8224_ = v_x_8220_;
                        v_isShared_8225_ = v_isSharedCheck_8230_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8222_);
                        lean_dec(v_x_8220_);
                        v___x_8224_ = lean_box(0);
                        v_isShared_8225_ = v_isSharedCheck_8230_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8231_ = lean_ctor_get(v_x_8220_, 0);
                    v_isSharedCheck_8240_ = (!lean_is_exclusive(v_x_8220_)) as u8;
                    if v_isSharedCheck_8240_ == 0 {
                        v___x_8233_ = v_x_8220_;
                        v_isShared_8234_ = v_isSharedCheck_8240_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8231_);
                        lean_dec(v_x_8220_);
                        v___x_8233_ = lean_box(0);
                        v_isShared_8234_ = v_isSharedCheck_8240_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8225_ == 0 {
                    v___x_8227_ = v___x_8224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8229_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8229_, 0, v_a_8222_);
                    v___x_8227_ = v_reuseFailAlloc_8229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8228_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8228_, 0, v___x_8227_);
                return v___x_8228_;
            }
            3 => {
                v___x_8235_ = l_Std_Http_Response_Builder_body___redArg(v_builder_8219_, v_a_8231_);
                if v_isShared_8234_ == 0 {
                    lean_ctor_set(v___x_8233_, 0, v___x_8235_);
                    v___x_8237_ = v___x_8233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8239_, 0, v___x_8235_);
                    v___x_8237_ = v_reuseFailAlloc_8239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8238_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8238_, 0, v___x_8237_);
                return v___x_8238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_stream___lam__0___boxed(
    mut v_builder_8241_: *mut LeanObject,
    mut v_x_8242_: *mut LeanObject,
    mut v___y_8243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8244_: *mut LeanObject = core::ptr::null_mut();
    v_res_8244_ = l_Std_Http_Response_Builder_stream___lam__0(v_builder_8241_, v_x_8242_);
    lean_dec_ref(v_builder_8241_);
    return v_res_8244_;
}
pub unsafe fn l_Std_Http_Response_Builder_stream(
    mut v_builder_8245_: *mut LeanObject,
    mut v_gen_8246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: u8 = 0;
    let mut v___x_8252_: *mut LeanObject = core::ptr::null_mut();
    v___x_8248_ = l_Std_Http_Body_stream(v_gen_8246_);
    v___f_8249_ = lean_alloc_closure(
        l_Std_Http_Response_Builder_stream___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8249_, 0, v_builder_8245_);
    v___x_8250_ = lean_unsigned_to_nat(0);
    v___x_8251_ = 0;
    v___x_8252_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8250_,
        v___x_8251_,
        v___x_8248_,
        v___f_8249_,
    );
    return v___x_8252_;
}
pub unsafe fn l_Std_Http_Response_Builder_stream___boxed(
    mut v_builder_8253_: *mut LeanObject,
    mut v_gen_8254_: *mut LeanObject,
    mut v_a_8255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8256_: *mut LeanObject = core::ptr::null_mut();
    v_res_8256_ = l_Std_Http_Response_Builder_stream(v_builder_8253_, v_gen_8254_);
    return v_res_8256_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
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
    res = runtime_initialize_Std_Http_Data_Chunk(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Body_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
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
    res = initialize_Std_Http_Data_Chunk(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data_Body_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data_Body_Any(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Stream(builtin);
}
