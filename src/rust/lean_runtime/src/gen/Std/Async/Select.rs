// Lean compiler output
// Module: Std.Async.Select
// Imports: Init.Data.Random Std.Async.Basic Init.Data.ByteArray.Extra Init.Data.Array.Lemmas Init.Omega
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::ByteArray::Extra::{
    initialize_Init_Data_ByteArray_Extra, l_ByteArray_toUInt64LE_x21,
    runtime_initialize_Init_Data_ByteArray_Extra,
};
use crate::r#gen::Init::Data::Random::{
    initialize_Init_Data_Random, l_mkStdGen, l_stdNext, l_stdRange,
    runtime_initialize_Init_Data_Random,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed,
};
use crate::r#gen::Std::Async::Basic::{
    initialize_Std_Async_Basic,
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    runtime_initialize_Std_Async_Basic,
};
use crate::lean_imports_rs::Init::Core::{lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_swap, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mod, lean_nat_mul, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::IO::{lean_io_bind_task, lean_io_get_random_bytes};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Std_Async_Waiter_race___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Waiter_race___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Waiter_race___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Waiter_race___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value: LeanStringObject<44> =
    LeanStringObject {
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
            116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100,
            32, 116, 111, 32, 116, 104, 101, 32, 65, 115, 121, 110, 99, 32, 119, 97, 115, 32, 100,
            114, 111, 112, 112, 101, 100, 0,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Selectable_one___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___lam__2___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___lam__2___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Selectable_one___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___lam__2___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4 as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___closed__0_value: LeanStringObject<48> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            83, 101, 108, 101, 99, 116, 97, 98, 108, 101, 46, 111, 110, 101, 32, 114, 101, 113,
            117, 105, 114, 101, 115, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 101,
            32, 83, 101, 108, 101, 99, 116, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_one___redArg___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Selectable_one___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_one___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1_value: LeanCtorObject<1> =
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
            l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_tryOne___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Selectable_tryOne___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_tryOne___redArg___closed__0_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Selectable_combine___redArg___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Selectable_combine___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Async_Selectable_combine___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_combine___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_Selectable_combine___redArg___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut LeanObject)],
    };
pub static mut l_Std_Async_Selectable_combine___redArg___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selectable_combine___redArg___boxed__const__1_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Async_Waiter_withPromise___redArg(
    mut v_w_2250_: *mut LeanObject,
    mut v_p_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v_unused_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_2252_ = lean_ctor_get(v_w_2250_, 0);
                v_isSharedCheck_2259_ = (!lean_is_exclusive(v_w_2250_)) as u8;
                if v_isSharedCheck_2259_ == 0 {
                    v_unused_2260_ = lean_ctor_get(v_w_2250_, 1);
                    lean_dec(v_unused_2260_);
                    v___x_2254_ = v_w_2250_;
                    v_isShared_2255_ = v_isSharedCheck_2259_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_finished_2252_);
                    lean_dec(v_w_2250_);
                    v___x_2254_ = lean_box(0);
                    v_isShared_2255_ = v_isSharedCheck_2259_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2255_ == 0 {
                    lean_ctor_set(v___x_2254_, 1, v_p_2251_);
                    v___x_2257_ = v___x_2254_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_finished_2252_);
                    lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_p_2251_);
                    v___x_2257_ = v_reuseFailAlloc_2258_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_withPromise(
    mut v_00_u03b1_2261_: *mut LeanObject,
    mut v_00_u03b2_2262_: *mut LeanObject,
    mut v_w_2263_: *mut LeanObject,
    mut v_p_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2272_: u8 = 0;
    let mut v_unused_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_2265_ = lean_ctor_get(v_w_2263_, 0);
                v_isSharedCheck_2272_ = (!lean_is_exclusive(v_w_2263_)) as u8;
                if v_isSharedCheck_2272_ == 0 {
                    v_unused_2273_ = lean_ctor_get(v_w_2263_, 1);
                    lean_dec(v_unused_2273_);
                    v___x_2267_ = v_w_2263_;
                    v_isShared_2268_ = v_isSharedCheck_2272_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_finished_2265_);
                    lean_dec(v_w_2263_);
                    v___x_2267_ = lean_box(0);
                    v_isShared_2268_ = v_isSharedCheck_2272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2268_ == 0 {
                    lean_ctor_set(v___x_2267_, 1, v_p_2264_);
                    v___x_2270_ = v___x_2267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_finished_2265_);
                    lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_p_2264_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___redArg___lam__0(mut v_s_2274_: u8) -> *mut LeanObject {
    let mut v___y_2276_: u8 = 0;
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: u8 = 0;
    let mut v___x_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_s_2274_ == 0 {
                    v___x_2281_ = 1;
                    v___y_2276_ = v___x_2281_;
                    state = 1;
                    continue;
                } else {
                    v___x_2282_ = 0;
                    v___y_2276_ = v___x_2282_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2277_ = 1;
                v___x_2278_ = lean_box((v___y_2276_) as usize);
                v___x_2279_ = lean_box((v___x_2277_) as usize);
                v___x_2280_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2280_, 0, v___x_2278_);
                lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                return v___x_2280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___redArg___lam__0___boxed(
    mut v_s_2283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_2284_: u8 = 0;
    let mut v_res_2285_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_2284_ = (lean_unbox(v_s_2283_) as u8);
    v_res_2285_ = l_Std_Async_Waiter_race___redArg___lam__0(v_s_boxed_2284_);
    return v_res_2285_;
}
pub unsafe fn l_Std_Async_Waiter_race___redArg___lam__1(
    mut v_lose_2286_: *mut LeanObject,
    mut v_win_2287_: *mut LeanObject,
    mut v_promise_2288_: *mut LeanObject,
    mut v_first_2289_: u8,
) -> *mut LeanObject {
    if v_first_2289_ == 0 {
        lean_dec(v_promise_2288_);
        lean_dec(v_win_2287_);
        lean_inc(v_lose_2286_);
        return v_lose_2286_;
    } else {
        let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
        v___x_2290_ = lean_apply_1(v_win_2287_, v_promise_2288_);
        return v___x_2290_;
    }
}
pub unsafe fn l_Std_Async_Waiter_race___redArg___lam__1___boxed(
    mut v_lose_2291_: *mut LeanObject,
    mut v_win_2292_: *mut LeanObject,
    mut v_promise_2293_: *mut LeanObject,
    mut v_first_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_first_boxed_2295_: u8 = 0;
    let mut v_res_2296_: *mut LeanObject = core::ptr::null_mut();
    v_first_boxed_2295_ = (lean_unbox(v_first_2294_) as u8);
    v_res_2296_ = l_Std_Async_Waiter_race___redArg___lam__1(
        v_lose_2291_,
        v_win_2292_,
        v_promise_2293_,
        v_first_boxed_2295_,
    );
    lean_dec(v_lose_2291_);
    return v_res_2296_;
}
pub unsafe fn l_Std_Async_Waiter_race___redArg(
    mut v_inst_2298_: *mut LeanObject,
    mut v_inst_2299_: *mut LeanObject,
    mut v_w_2300_: *mut LeanObject,
    mut v_lose_2301_: *mut LeanObject,
    mut v_win_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2303_ = lean_ctor_get(v_inst_2298_, 1);
    lean_inc(v_toBind_2303_);
    lean_dec_ref(v_inst_2298_);
    v_finished_2304_ = lean_ctor_get(v_w_2300_, 0);
    lean_inc(v_finished_2304_);
    v_promise_2305_ = lean_ctor_get(v_w_2300_, 1);
    lean_inc(v_promise_2305_);
    lean_dec_ref(v_w_2300_);
    v___f_2306_ = l_Std_Async_Waiter_race___redArg___closed__0;
    v___f_2307_ = lean_alloc_closure(
        l_Std_Async_Waiter_race___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2307_, 0, v_lose_2301_);
    lean_closure_set(v___f_2307_, 1, v_win_2302_);
    lean_closure_set(v___f_2307_, 2, v_promise_2305_);
    v___x_2308_ = lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___x_2308_, 0, lean_box(0));
    lean_closure_set(v___x_2308_, 1, lean_box(0));
    lean_closure_set(v___x_2308_, 2, lean_box(0));
    lean_closure_set(v___x_2308_, 3, v_finished_2304_);
    lean_closure_set(v___x_2308_, 4, v___f_2306_);
    v___x_2309_ = lean_apply_2(v_inst_2299_, lean_box(0), v___x_2308_);
    v___x_2310_ = lean_apply_4(
        v_toBind_2303_,
        lean_box(0),
        lean_box(0),
        v___x_2309_,
        v___f_2307_,
    );
    return v___x_2310_;
}
pub unsafe fn l_Std_Async_Waiter_race(
    mut v_m_2311_: *mut LeanObject,
    mut v_00_u03b1_2312_: *mut LeanObject,
    mut v_00_u03b2_2313_: *mut LeanObject,
    mut v_inst_2314_: *mut LeanObject,
    mut v_inst_2315_: *mut LeanObject,
    mut v_w_2316_: *mut LeanObject,
    mut v_lose_2317_: *mut LeanObject,
    mut v_win_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_Std_Async_Waiter_race___redArg(
        v_inst_2314_,
        v_inst_2315_,
        v_w_2316_,
        v_lose_2317_,
        v_win_2318_,
    );
    return v___x_2319_;
}
pub unsafe fn l_Std_Async_Waiter_checkFinished___redArg(
    mut v_inst_2320_: *mut LeanObject,
    mut v_w_2321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    v_finished_2322_ = lean_ctor_get(v_w_2321_, 0);
    lean_inc(v_finished_2322_);
    lean_dec_ref(v_w_2321_);
    v___x_2323_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2323_, 0, lean_box(0));
    lean_closure_set(v___x_2323_, 1, lean_box(0));
    lean_closure_set(v___x_2323_, 2, v_finished_2322_);
    v___x_2324_ = lean_apply_2(v_inst_2320_, lean_box(0), v___x_2323_);
    return v___x_2324_;
}
pub unsafe fn l_Std_Async_Waiter_checkFinished(
    mut v_m_2325_: *mut LeanObject,
    mut v_00_u03b1_2326_: *mut LeanObject,
    mut v_inst_2327_: *mut LeanObject,
    mut v_inst_2328_: *mut LeanObject,
    mut v_w_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    v_finished_2330_ = lean_ctor_get(v_w_2329_, 0);
    lean_inc(v_finished_2330_);
    lean_dec_ref(v_w_2329_);
    v___x_2331_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2331_, 0, lean_box(0));
    lean_closure_set(v___x_2331_, 1, lean_box(0));
    lean_closure_set(v___x_2331_, 2, v_finished_2330_);
    v___x_2332_ = lean_apply_2(v_inst_2328_, lean_box(0), v___x_2331_);
    return v___x_2332_;
}
pub unsafe fn l_Std_Async_Waiter_checkFinished___boxed(
    mut v_m_2333_: *mut LeanObject,
    mut v_00_u03b1_2334_: *mut LeanObject,
    mut v_inst_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_w_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Std_Async_Waiter_checkFinished(
        v_m_2333_,
        v_00_u03b1_2334_,
        v_inst_2335_,
        v_inst_2336_,
        v_w_2337_,
    );
    lean_dec_ref(v_inst_2335_);
    return v_res_2338_;
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(
    mut v_genLo_2339_: *mut LeanObject,
    mut v_genMag_2340_: *mut LeanObject,
    mut v_x_2341_: *mut LeanObject,
    mut v_x_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2344_: u8 = 0;
    let mut v_fst_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_x27_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2343_ = lean_unsigned_to_nat(0);
                v_isZero_2344_ = lean_nat_dec_eq(v_x_2341_, v_zero_2343_);
                if v_isZero_2344_ == 1 {
                    lean_dec(v_x_2341_);
                    return v_x_2342_;
                } else {
                    v_fst_2345_ = lean_ctor_get(v_x_2342_, 0);
                    lean_inc(v_fst_2345_);
                    v_snd_2346_ = lean_ctor_get(v_x_2342_, 1);
                    lean_inc(v_snd_2346_);
                    lean_dec_ref(v_x_2342_);
                    v___x_2347_ = l_stdNext(v_snd_2346_);
                    v_fst_2348_ = lean_ctor_get(v___x_2347_, 0);
                    v_snd_2349_ = lean_ctor_get(v___x_2347_, 1);
                    v_isSharedCheck_2363_ = (!lean_is_exclusive(v___x_2347_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2351_ = v___x_2347_;
                        v_isShared_2352_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2349_);
                        lean_inc(v_fst_2348_);
                        lean_dec(v___x_2347_);
                        v___x_2351_ = lean_box(0);
                        v_isShared_2352_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2353_ = lean_nat_mul(v_fst_2345_, v_genMag_2340_);
                lean_dec(v_fst_2345_);
                v___x_2354_ = lean_nat_sub(v_fst_2348_, v_genLo_2339_);
                lean_dec(v_fst_2348_);
                v_v_x27_2355_ = lean_nat_add(v___x_2353_, v___x_2354_);
                lean_dec(v___x_2354_);
                lean_dec(v___x_2353_);
                v___x_2356_ = lean_nat_div(v_x_2341_, v_genMag_2340_);
                lean_dec(v_x_2341_);
                v___x_2357_ = lean_unsigned_to_nat(1);
                v___x_2358_ = lean_nat_sub(v___x_2356_, v___x_2357_);
                lean_dec(v___x_2356_);
                if v_isShared_2352_ == 0 {
                    lean_ctor_set(v___x_2351_, 0, v_v_x27_2355_);
                    v___x_2360_ = v___x_2351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_v_x27_2355_);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2349_);
                    v___x_2360_ = v_reuseFailAlloc_2362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_2341_ = v___x_2358_;
                v_x_2342_ = v___x_2360_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0___boxed(
    mut v_genLo_2364_: *mut LeanObject,
    mut v_genMag_2365_: *mut LeanObject,
    mut v_x_2366_: *mut LeanObject,
    mut v_x_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2368_: *mut LeanObject = core::ptr::null_mut();
    v_res_2368_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(v_genLo_2364_, v_genMag_2365_, v_x_2366_, v_x_2367_);
    lean_dec(v_genMag_2365_);
    lean_dec(v_genLo_2364_);
    return v_res_2368_;
}
pub unsafe fn l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(
    mut v_g_2369_: *mut LeanObject,
    mut v_lo_2370_: *mut LeanObject,
    mut v_hi_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_genMag_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tgtMag_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_x27_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v___x_2399_: u8 = 0;
    let mut v___y_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2399_ = lean_nat_dec_lt(v_hi_2371_, v_lo_2370_);
                if v___x_2399_ == 0 {
                    v___y_2401_ = v_lo_2370_;
                    state = 4;
                    continue;
                } else {
                    v___y_2401_ = v_hi_2371_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_2375_ = l_stdRange;
                v_fst_2376_ = lean_ctor_get(v___x_2375_, 0);
                v_snd_2377_ = lean_ctor_get(v___x_2375_, 1);
                v___x_2378_ = lean_nat_sub(v_snd_2377_, v_fst_2376_);
                v___x_2379_ = lean_unsigned_to_nat(1);
                v_genMag_2380_ = lean_nat_add(v___x_2378_, v___x_2379_);
                lean_dec(v___x_2378_);
                v_q_2381_ = lean_unsigned_to_nat(1000);
                v___x_2382_ = lean_nat_sub(v___y_2374_, v___y_2373_);
                v_k_2383_ = lean_nat_add(v___x_2382_, v___x_2379_);
                lean_dec(v___x_2382_);
                v_tgtMag_2384_ = lean_nat_mul(v_k_2383_, v_q_2381_);
                v___x_2385_ = lean_unsigned_to_nat(0);
                v___x_2386_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2386_, 0, v___x_2385_);
                lean_ctor_set(v___x_2386_, 1, v_g_2369_);
                v___x_2387_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0_spec__0(v_fst_2376_, v_genMag_2380_, v_tgtMag_2384_, v___x_2386_);
                lean_dec(v_genMag_2380_);
                v_fst_2388_ = lean_ctor_get(v___x_2387_, 0);
                v_snd_2389_ = lean_ctor_get(v___x_2387_, 1);
                v_isSharedCheck_2398_ = (!lean_is_exclusive(v___x_2387_)) as u8;
                if v_isSharedCheck_2398_ == 0 {
                    v___x_2391_ = v___x_2387_;
                    v_isShared_2392_ = v_isSharedCheck_2398_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2389_);
                    lean_inc(v_fst_2388_);
                    lean_dec(v___x_2387_);
                    v___x_2391_ = lean_box(0);
                    v_isShared_2392_ = v_isSharedCheck_2398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2393_ = lean_nat_mod(v_fst_2388_, v_k_2383_);
                lean_dec(v_k_2383_);
                lean_dec(v_fst_2388_);
                v_v_x27_2394_ = lean_nat_add(v___y_2373_, v___x_2393_);
                lean_dec(v___x_2393_);
                if v_isShared_2392_ == 0 {
                    lean_ctor_set(v___x_2391_, 0, v_v_x27_2394_);
                    v___x_2396_ = v___x_2391_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_v_x27_2394_);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_snd_2389_);
                    v___x_2396_ = v_reuseFailAlloc_2397_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2396_;
            }
            4 => {
                if v___x_2399_ == 0 {
                    v___y_2373_ = v___y_2401_;
                    v___y_2374_ = v_hi_2371_;
                    state = 1;
                    continue;
                } else {
                    v___y_2373_ = v___y_2401_;
                    v___y_2374_ = v_lo_2370_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0___boxed(
    mut v_g_2402_: *mut LeanObject,
    mut v_lo_2403_: *mut LeanObject,
    mut v_hi_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2405_: *mut LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(
        v_g_2402_, v_lo_2403_, v_hi_2404_,
    );
    lean_dec(v_hi_2404_);
    lean_dec(v_lo_2403_);
    return v_res_2405_;
}
pub unsafe fn l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(
    mut v_xs_2406_: *mut LeanObject,
    mut v_gen_2407_: *mut LeanObject,
    mut v_i_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2409_ = lean_array_get_size(v_xs_2406_);
                v___x_2410_ = lean_unsigned_to_nat(1);
                v___x_2411_ = lean_nat_sub(v___x_2409_, v___x_2410_);
                v___x_2412_ = lean_nat_dec_lt(v_i_2408_, v___x_2411_);
                if v___x_2412_ == 0 {
                    lean_dec(v___x_2411_);
                    lean_dec(v_i_2408_);
                    lean_dec_ref(v_gen_2407_);
                    return v_xs_2406_;
                } else {
                    v___x_2413_ = l_randNat___at___00__private_Std_Async_Select_0__Std_Async_shuffleIt_go_spec__0(v_gen_2407_, v_i_2408_, v___x_2411_);
                    lean_dec(v___x_2411_);
                    v_fst_2414_ = lean_ctor_get(v___x_2413_, 0);
                    lean_inc(v_fst_2414_);
                    v_snd_2415_ = lean_ctor_get(v___x_2413_, 1);
                    lean_inc(v_snd_2415_);
                    lean_dec_ref(v___x_2413_);
                    v_xs_2416_ = lean_array_swap(v_xs_2406_, v_i_2408_, v_fst_2414_);
                    lean_dec(v_fst_2414_);
                    v___x_2417_ = lean_nat_add(v_i_2408_, v___x_2410_);
                    lean_dec(v_i_2408_);
                    v_xs_2406_ = v_xs_2416_;
                    v_gen_2407_ = v_snd_2415_;
                    v_i_2408_ = v___x_2417_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Select_0__Std_Async_shuffleIt_go(
    mut v_00_u03b1_2419_: *mut LeanObject,
    mut v_xs_2420_: *mut LeanObject,
    mut v_gen_2421_: *mut LeanObject,
    mut v_i_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    v___x_2423_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(
        v_xs_2420_,
        v_gen_2421_,
        v_i_2422_,
    );
    return v___x_2423_;
}
pub unsafe fn l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter___redArg(
    mut v_x_2424_: *mut LeanObject,
    mut v_h__1_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2426_ = lean_ctor_get(v_x_2424_, 0);
    lean_inc(v_fst_2426_);
    v_snd_2427_ = lean_ctor_get(v_x_2424_, 1);
    lean_inc(v_snd_2427_);
    lean_dec_ref(v_x_2424_);
    v___x_2428_ = lean_apply_2(v_h__1_2425_, v_fst_2426_, v_snd_2427_);
    return v___x_2428_;
}
pub unsafe fn l___private_Std_Async_Select_0__Std_Async_shuffleIt_go_match__1_splitter(
    mut v_motive_2429_: *mut LeanObject,
    mut v_x_2430_: *mut LeanObject,
    mut v_h__1_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2432_ = lean_ctor_get(v_x_2430_, 0);
    lean_inc(v_fst_2432_);
    v_snd_2433_ = lean_ctor_get(v_x_2430_, 1);
    lean_inc(v_snd_2433_);
    lean_dec_ref(v_x_2430_);
    v___x_2434_ = lean_apply_2(v_h__1_2431_, v_fst_2432_, v_snd_2433_);
    return v___x_2434_;
}
pub unsafe fn l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(
    mut v_xs_2435_: *mut LeanObject,
    mut v_gen_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = lean_unsigned_to_nat(0);
    v___x_2438_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt_go___redArg(
        v_xs_2435_,
        v_gen_2436_,
        v___x_2437_,
    );
    return v___x_2438_;
}
pub unsafe fn l___private_Std_Async_Select_0__Std_Async_shuffleIt(
    mut v_00_u03b1_2439_: *mut LeanObject,
    mut v_xs_2440_: *mut LeanObject,
    mut v_gen_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2442_ =
        l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(v_xs_2440_, v_gen_2441_);
    return v___x_2442_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(
    mut v_e_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2448_: u8 = 0;
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut v_a_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_2443_) == 0 {
                    v_a_2445_ = lean_ctor_get(v_e_2443_, 0);
                    v_isSharedCheck_2454_ = (!lean_is_exclusive(v_e_2443_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2447_ = v_e_2443_;
                        v_isShared_2448_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2445_);
                        lean_dec(v_e_2443_);
                        v___x_2447_ = lean_box(0);
                        v_isShared_2448_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2455_ = lean_ctor_get(v_e_2443_, 0);
                    v_isSharedCheck_2462_ = (!lean_is_exclusive(v_e_2443_)) as u8;
                    if v_isSharedCheck_2462_ == 0 {
                        v___x_2457_ = v_e_2443_;
                        v_isShared_2458_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2455_);
                        lean_dec(v_e_2443_);
                        v___x_2457_ = lean_box(0);
                        v_isShared_2458_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2449_ = lean_io_error_to_string(v_a_2445_);
                v___x_2450_ = lean_mk_io_user_error(v___x_2449_);
                if v_isShared_2448_ == 0 {
                    lean_ctor_set_tag(v___x_2447_, 1);
                    lean_ctor_set(v___x_2447_, 0, v___x_2450_);
                    v___x_2452_ = v___x_2447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2452_;
            }
            3 => {
                if v_isShared_2458_ == 0 {
                    lean_ctor_set_tag(v___x_2457_, 0);
                    v___x_2460_ = v___x_2457_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg___boxed(
    mut v_e_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2465_: *mut LeanObject = core::ptr::null_mut();
    v_res_2465_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_e_2463_);
    return v_res_2465_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(
    mut v_00_u03b1_2466_: *mut LeanObject,
    mut v_e_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_e_2467_);
    return v___x_2469_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___boxed(
    mut v_00_u03b1_2470_: *mut LeanObject,
    mut v_e_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2473_: *mut LeanObject = core::ptr::null_mut();
    v_res_2473_ =
        l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1(v_00_u03b1_2470_, v_e_2471_);
    return v_res_2473_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__0(
    mut v___x_2474_: *mut LeanObject,
    mut v_x_2475_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2475_) == 0 {
        let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
        v___x_2476_ = lean_mk_io_user_error(v___x_2474_);
        v___x_2477_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2477_, 0, v___x_2476_);
        return v___x_2477_;
    } else {
        let mut v_val_2478_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2474_);
        v_val_2478_ = lean_ctor_get(v_x_2475_, 0);
        lean_inc(v_val_2478_);
        return v_val_2478_;
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__0___boxed(
    mut v___x_2479_: *mut LeanObject,
    mut v_x_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Std_Async_Selectable_one___redArg___lam__0(v___x_2479_, v_x_2480_);
    lean_dec(v_x_2480_);
    return v_res_2481_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__1(
    mut v___f_2482_: *mut LeanObject,
    mut v_x_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v_a_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: u8 = 0;
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2483_) == 0 {
                    lean_dec_ref(v___f_2482_);
                    v_a_2485_ = lean_ctor_get(v_x_2483_, 0);
                    v_isSharedCheck_2493_ = (!lean_is_exclusive(v_x_2483_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2487_ = v_x_2483_;
                        v_isShared_2488_ = v_isSharedCheck_2493_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2485_);
                        lean_dec(v_x_2483_);
                        v___x_2487_ = lean_box(0);
                        v_isShared_2488_ = v_isSharedCheck_2493_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2494_ = lean_ctor_get(v_x_2483_, 0);
                    lean_inc(v_a_2494_);
                    lean_dec_ref_known(v_x_2483_, 1);
                    if lean_obj_tag(v_a_2494_) == 0 {
                        lean_dec_ref(v___f_2482_);
                        v_a_2495_ = lean_ctor_get(v_a_2494_, 0);
                        v_isSharedCheck_2503_ = (!lean_is_exclusive(v_a_2494_)) as u8;
                        if v_isSharedCheck_2503_ == 0 {
                            v___x_2497_ = v_a_2494_;
                            v_isShared_2498_ = v_isSharedCheck_2503_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2495_);
                            lean_dec(v_a_2494_);
                            v___x_2497_ = lean_box(0);
                            v_isShared_2498_ = v_isSharedCheck_2503_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2504_ = lean_ctor_get(v_a_2494_, 0);
                        lean_inc(v_a_2504_);
                        lean_dec_ref_known(v_a_2494_, 1);
                        v___x_2505_ = lean_io_promise_result_opt(v_a_2504_);
                        lean_dec(v_a_2504_);
                        v___x_2506_ = lean_unsigned_to_nat(0);
                        v___x_2507_ = 0;
                        v___x_2508_ =
                            lean_task_map(v___f_2482_, v___x_2505_, v___x_2506_, v___x_2507_);
                        v___x_2509_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2509_, 0, v___x_2508_);
                        return v___x_2509_;
                    }
                }
            }
            1 => {
                if v_isShared_2488_ == 0 {
                    v___x_2490_ = v___x_2487_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2485_);
                    v___x_2490_ = v_reuseFailAlloc_2492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2491_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2491_, 0, v___x_2490_);
                return v___x_2491_;
            }
            3 => {
                if v_isShared_2498_ == 0 {
                    v___x_2500_ = v___x_2497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2495_);
                    v___x_2500_ = v_reuseFailAlloc_2502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2501_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2501_, 0, v___x_2500_);
                return v___x_2501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__1___boxed(
    mut v___f_2510_: *mut LeanObject,
    mut v_x_2511_: *mut LeanObject,
    mut v___y_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2513_: *mut LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Std_Async_Selectable_one___redArg___lam__1(v___f_2510_, v_x_2511_);
    return v_res_2513_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__2(
    mut v_x_2519_: *mut LeanObject,
    mut v_x_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2530_: u8 = 0;
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v___f_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_unused_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2520_) == 0 {
                    lean_dec_ref(v_x_2519_);
                    v_a_2522_ = lean_ctor_get(v_x_2520_, 0);
                    v_isSharedCheck_2530_ = (!lean_is_exclusive(v_x_2520_)) as u8;
                    if v_isSharedCheck_2530_ == 0 {
                        v___x_2524_ = v_x_2520_;
                        v_isShared_2525_ = v_isSharedCheck_2530_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2522_);
                        lean_dec(v_x_2520_);
                        v___x_2524_ = lean_box(0);
                        v_isShared_2525_ = v_isSharedCheck_2530_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2542_ = (!lean_is_exclusive(v_x_2520_)) as u8;
                    if v_isSharedCheck_2542_ == 0 {
                        v_unused_2543_ = lean_ctor_get(v_x_2520_, 0);
                        lean_dec(v_unused_2543_);
                        v___x_2532_ = v_x_2520_;
                        v_isShared_2533_ = v_isSharedCheck_2542_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_2520_);
                        v___x_2532_ = lean_box(0);
                        v_isShared_2533_ = v_isSharedCheck_2542_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2525_ == 0 {
                    v___x_2527_ = v___x_2524_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2522_);
                    v___x_2527_ = v_reuseFailAlloc_2529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2528_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2528_, 0, v___x_2527_);
                return v___x_2528_;
            }
            3 => {
                v___f_2534_ = l_Std_Async_Selectable_one___redArg___lam__2___closed__2;
                if v_isShared_2533_ == 0 {
                    lean_ctor_set(v___x_2532_, 0, v_x_2519_);
                    v___x_2536_ = v___x_2532_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_x_2519_);
                    v___x_2536_ = v_reuseFailAlloc_2541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2537_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2537_, 0, v___x_2536_);
                v___x_2538_ = lean_unsigned_to_nat(0);
                v___x_2539_ = 0;
                v___x_2540_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2538_,
                    v___x_2539_,
                    v___x_2537_,
                    v___f_2534_,
                );
                return v___x_2540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__2___boxed(
    mut v_x_2544_: *mut LeanObject,
    mut v_x_2545_: *mut LeanObject,
    mut v___y_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2547_: *mut LeanObject = core::ptr::null_mut();
    v_res_2547_ = l_Std_Async_Selectable_one___redArg___lam__2(v_x_2544_, v_x_2545_);
    return v_res_2547_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__3(
    mut v___x_2548_: *mut LeanObject,
    mut v_a_2549_: *mut LeanObject,
    mut v___f_2550_: *mut LeanObject,
    mut v_x_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2573_: u8 = 0;
    let mut v_unused_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2551_) == 0 {
                    lean_dec_ref(v___f_2550_);
                    v_a_2553_ = lean_ctor_get(v_x_2551_, 0);
                    v_isSharedCheck_2561_ = (!lean_is_exclusive(v_x_2551_)) as u8;
                    if v_isSharedCheck_2561_ == 0 {
                        v___x_2555_ = v_x_2551_;
                        v_isShared_2556_ = v_isSharedCheck_2561_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2553_);
                        lean_dec(v_x_2551_);
                        v___x_2555_ = lean_box(0);
                        v_isShared_2556_ = v_isSharedCheck_2561_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2573_ = (!lean_is_exclusive(v_x_2551_)) as u8;
                    if v_isSharedCheck_2573_ == 0 {
                        v_unused_2574_ = lean_ctor_get(v_x_2551_, 0);
                        lean_dec(v_unused_2574_);
                        v___x_2563_ = v_x_2551_;
                        v_isShared_2564_ = v_isSharedCheck_2573_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_2551_);
                        v___x_2563_ = lean_box(0);
                        v_isShared_2564_ = v_isSharedCheck_2573_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2556_ == 0 {
                    v___x_2558_ = v___x_2555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2553_);
                    v___x_2558_ = v_reuseFailAlloc_2560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2559_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2559_, 0, v___x_2558_);
                return v___x_2559_;
            }
            3 => {
                v___x_2565_ = lean_io_promise_resolve(v___x_2548_, v_a_2549_);
                if v_isShared_2564_ == 0 {
                    lean_ctor_set(v___x_2563_, 0, v___x_2565_);
                    v___x_2567_ = v___x_2563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2565_);
                    v___x_2567_ = v_reuseFailAlloc_2572_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2568_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                v___x_2569_ = lean_unsigned_to_nat(0);
                v___x_2570_ = 0;
                v___x_2571_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2569_,
                    v___x_2570_,
                    v___x_2568_,
                    v___f_2550_,
                );
                return v___x_2571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__3___boxed(
    mut v___x_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
    mut v___f_2577_: *mut LeanObject,
    mut v_x_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2580_: *mut LeanObject = core::ptr::null_mut();
    v_res_2580_ = l_Std_Async_Selectable_one___redArg___lam__3(
        v___x_2575_,
        v_a_2576_,
        v___f_2577_,
        v_x_2578_,
    );
    lean_dec(v_a_2576_);
    return v_res_2580_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__4(
    mut v___x_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2597_: u8 = 0;
    let mut v_unused_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_2582_) == 0 {
                    v_a_2583_ = lean_ctor_get(v___y_2582_, 0);
                    v_isSharedCheck_2590_ = (!lean_is_exclusive(v___y_2582_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v___x_2585_ = v___y_2582_;
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2583_);
                        lean_dec(v___y_2582_);
                        v___x_2585_ = lean_box(0);
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2597_ = (!lean_is_exclusive(v___y_2582_)) as u8;
                    if v_isSharedCheck_2597_ == 0 {
                        v_unused_2598_ = lean_ctor_get(v___y_2582_, 0);
                        lean_dec(v_unused_2598_);
                        v___x_2592_ = v___y_2582_;
                        v_isShared_2593_ = v_isSharedCheck_2597_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___y_2582_);
                        v___x_2592_ = lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2597_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2586_ == 0 {
                    v___x_2588_ = v___x_2585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2588_;
            }
            3 => {
                if v_isShared_2593_ == 0 {
                    lean_ctor_set(v___x_2592_, 0, v___x_2581_);
                    v___x_2595_ = v___x_2592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2581_);
                    v___x_2595_ = v_reuseFailAlloc_2596_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(
    mut v_a_2599_: *mut LeanObject,
    mut v_x_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2600_) == 0 {
                    v_a_2602_ = lean_ctor_get(v_x_2600_, 0);
                    v_isSharedCheck_2612_ = (!lean_is_exclusive(v_x_2600_)) as u8;
                    if v_isSharedCheck_2612_ == 0 {
                        v___x_2604_ = v_x_2600_;
                        v_isShared_2605_ = v_isSharedCheck_2612_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2602_);
                        lean_dec(v_x_2600_);
                        v___x_2604_ = lean_box(0);
                        v_isShared_2605_ = v_isSharedCheck_2612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2613_, 0, v_x_2600_);
                    return v___x_2613_;
                }
            }
            1 => {
                if v_isShared_2605_ == 0 {
                    v___x_2607_ = v___x_2604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2602_);
                    v___x_2607_ = v_reuseFailAlloc_2611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2608_ = lean_io_promise_resolve(v___x_2607_, v_a_2599_);
                v___x_2609_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2609_, 0, v___x_2608_);
                v___x_2610_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2610_, 0, v___x_2609_);
                return v___x_2610_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed(
    mut v_a_2614_: *mut LeanObject,
    mut v_x_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2617_: *mut LeanObject = core::ptr::null_mut();
    v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2(v_a_2614_, v_x_2615_);
    lean_dec(v_a_2614_);
    return v_res_2617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__1(
    mut v_a_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    v___x_2619_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2619_, 0, v_a_2618_);
    return v___x_2619_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(
    mut v_a_2620_: *mut LeanObject,
    mut v_x_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2626_: u8 = 0;
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2631_: u8 = 0;
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2621_) == 0 {
                    v_a_2623_ = lean_ctor_get(v_x_2621_, 0);
                    v_isSharedCheck_2631_ = (!lean_is_exclusive(v_x_2621_)) as u8;
                    if v_isSharedCheck_2631_ == 0 {
                        v___x_2625_ = v_x_2621_;
                        v_isShared_2626_ = v_isSharedCheck_2631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2623_);
                        lean_dec(v_x_2621_);
                        v___x_2625_ = lean_box(0);
                        v_isShared_2626_ = v_isSharedCheck_2631_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2632_ = lean_io_promise_resolve(v_x_2621_, v_a_2620_);
                    v___x_2633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2633_, 0, v___x_2632_);
                    v___x_2634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2634_, 0, v___x_2633_);
                    return v___x_2634_;
                }
            }
            1 => {
                if v_isShared_2626_ == 0 {
                    v___x_2628_ = v___x_2625_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2623_);
                    v___x_2628_ = v_reuseFailAlloc_2630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2629_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2629_, 0, v___x_2628_);
                return v___x_2629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed(
    mut v_a_2635_: *mut LeanObject,
    mut v_x_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2638_: *mut LeanObject = core::ptr::null_mut();
    v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0(v_a_2635_, v_x_2636_);
    lean_dec(v_a_2635_);
    return v_res_2638_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(
    mut v_a_2639_: *mut LeanObject,
    mut v___f_2640_: *mut LeanObject,
    mut v___x_2641_: u8,
    mut v___x_2642_: *mut LeanObject,
    mut v_a_2643_: u8,
    mut v___f_2644_: *mut LeanObject,
    mut v_x_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v_unused_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2645_) == 0 {
                    lean_dec_ref(v___f_2644_);
                    lean_dec_ref(v___f_2640_);
                    v_a_2647_ = lean_ctor_get(v_x_2645_, 0);
                    v_isSharedCheck_2655_ = (!lean_is_exclusive(v_x_2645_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v___x_2649_ = v_x_2645_;
                        v_isShared_2650_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2647_);
                        lean_dec(v_x_2645_);
                        v___x_2649_ = lean_box(0);
                        v_isShared_2650_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2667_ = (!lean_is_exclusive(v_x_2645_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v_unused_2668_ = lean_ctor_get(v_x_2645_, 0);
                        lean_dec(v_unused_2668_);
                        v___x_2657_ = v_x_2645_;
                        v_isShared_2658_ = v_isSharedCheck_2667_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_2645_);
                        v___x_2657_ = lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2667_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2650_ == 0 {
                    v___x_2652_ = v___x_2649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2647_);
                    v___x_2652_ = v_reuseFailAlloc_2654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2653_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2653_, 0, v___x_2652_);
                return v___x_2653_;
            }
            3 => {
                v___x_2659_ = lean_io_promise_result_opt(v_a_2639_);
                v___x_2660_ = lean_unsigned_to_nat(0);
                v___x_2661_ = lean_io_bind_task(v___x_2659_, v___f_2640_, v___x_2660_, v___x_2641_);
                lean_dec_ref(v___x_2661_);
                if v_isShared_2658_ == 0 {
                    lean_ctor_set(v___x_2657_, 0, v___x_2642_);
                    v___x_2663_ = v___x_2657_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2642_);
                    v___x_2663_ = v_reuseFailAlloc_2666_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2664_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2664_, 0, v___x_2663_);
                v___x_2665_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2660_,
                    v_a_2643_,
                    v___x_2664_,
                    v___f_2644_,
                );
                return v___x_2665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed(
    mut v_a_2669_: *mut LeanObject,
    mut v___f_2670_: *mut LeanObject,
    mut v___x_2671_: *mut LeanObject,
    mut v___x_2672_: *mut LeanObject,
    mut v_a_2673_: *mut LeanObject,
    mut v___f_2674_: *mut LeanObject,
    mut v_x_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10927__boxed_2677_: u8 = 0;
    let mut v_a_10929__boxed_2678_: u8 = 0;
    let mut v_res_2679_: *mut LeanObject = core::ptr::null_mut();
    v___x_10927__boxed_2677_ = (lean_unbox(v___x_2671_) as u8);
    v_a_10929__boxed_2678_ = (lean_unbox(v_a_2673_) as u8);
    v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8(v_a_2669_, v___f_2670_, v___x_10927__boxed_2677_, v___x_2672_, v_a_10929__boxed_2678_, v___f_2674_, v_x_2675_);
    lean_dec(v_a_2669_);
    return v_res_2679_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(
    mut v_a_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v___f_2682_: *mut LeanObject,
    mut v___x_2683_: u8,
    mut v___x_2684_: *mut LeanObject,
    mut v_a_2685_: u8,
    mut v___f_2686_: *mut LeanObject,
    mut v_x_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_selector_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v_a_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registerFn_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_unused_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2687_) == 0 {
                    lean_dec_ref(v___f_2686_);
                    lean_dec_ref(v___f_2682_);
                    lean_dec(v_a_2681_);
                    lean_dec_ref(v_a_2680_);
                    v_a_2689_ = lean_ctor_get(v_x_2687_, 0);
                    v_isSharedCheck_2697_ = (!lean_is_exclusive(v_x_2687_)) as u8;
                    if v_isSharedCheck_2697_ == 0 {
                        v___x_2691_ = v_x_2687_;
                        v_isShared_2692_ = v_isSharedCheck_2697_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2689_);
                        lean_dec(v_x_2687_);
                        v___x_2691_ = lean_box(0);
                        v_isShared_2692_ = v_isSharedCheck_2697_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_selector_2698_ = lean_ctor_get(v_a_2680_, 0);
                    v_isSharedCheck_2713_ = (!lean_is_exclusive(v_a_2680_)) as u8;
                    if v_isSharedCheck_2713_ == 0 {
                        v_unused_2714_ = lean_ctor_get(v_a_2680_, 1);
                        lean_dec(v_unused_2714_);
                        v___x_2700_ = v_a_2680_;
                        v_isShared_2701_ = v_isSharedCheck_2713_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_selector_2698_);
                        lean_dec(v_a_2680_);
                        v___x_2700_ = lean_box(0);
                        v_isShared_2701_ = v_isSharedCheck_2713_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2692_ == 0 {
                    v___x_2694_ = v___x_2691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2689_);
                    v___x_2694_ = v_reuseFailAlloc_2696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2695_, 0, v___x_2694_);
                return v___x_2695_;
            }
            3 => {
                v_a_2702_ = lean_ctor_get(v_x_2687_, 0);
                lean_inc_n(v_a_2702_, 2);
                lean_dec_ref_known(v_x_2687_, 1);
                v_registerFn_2703_ = lean_ctor_get(v_selector_2698_, 1);
                lean_inc_ref(v_registerFn_2703_);
                lean_dec_ref(v_selector_2698_);
                if v_isShared_2701_ == 0 {
                    lean_ctor_set(v___x_2700_, 1, v_a_2702_);
                    lean_ctor_set(v___x_2700_, 0, v_a_2681_);
                    v___x_2705_ = v___x_2700_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2681_);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_a_2702_);
                    v___x_2705_ = v_reuseFailAlloc_2712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2706_ = lean_apply_2(v_registerFn_2703_, v___x_2705_, lean_box(0));
                v___x_2707_ = lean_box((v___x_2683_) as usize);
                v___x_2708_ = lean_box((v_a_2685_) as usize);
                v___f_2709_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__8___boxed as *mut core::ffi::c_void, 8, 6);
                lean_closure_set(v___f_2709_, 0, v_a_2702_);
                lean_closure_set(v___f_2709_, 1, v___f_2682_);
                lean_closure_set(v___f_2709_, 2, v___x_2707_);
                lean_closure_set(v___f_2709_, 3, v___x_2684_);
                lean_closure_set(v___f_2709_, 4, v___x_2708_);
                lean_closure_set(v___f_2709_, 5, v___f_2686_);
                v___x_2710_ = lean_unsigned_to_nat(0);
                v___x_2711_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2710_,
                    v_a_2685_,
                    v___x_2706_,
                    v___f_2709_,
                );
                return v___x_2711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed(
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v___f_2717_: *mut LeanObject,
    mut v___x_2718_: *mut LeanObject,
    mut v___x_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
    mut v___f_2721_: *mut LeanObject,
    mut v_x_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10996__boxed_2724_: u8 = 0;
    let mut v_a_10998__boxed_2725_: u8 = 0;
    let mut v_res_2726_: *mut LeanObject = core::ptr::null_mut();
    v___x_10996__boxed_2724_ = (lean_unbox(v___x_2718_) as u8);
    v_a_10998__boxed_2725_ = (lean_unbox(v_a_2720_) as u8);
    v_res_2726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9(v_a_2715_, v_a_2716_, v___f_2717_, v___x_10996__boxed_2724_, v___x_2719_, v_a_10998__boxed_2725_, v___f_2721_, v_x_2722_);
    return v_res_2726_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: u8,
    mut v___f_2730_: *mut LeanObject,
    mut v_x_2731_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2731_) == 0 {
        let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_2730_);
        lean_dec(v_a_2728_);
        lean_dec_ref(v_a_2727_);
        v___x_2733_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2733_, 0, v_x_2731_);
        return v___x_2733_;
    } else {
        let mut v_cont_2734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_x_2731_, 1);
        v_cont_2734_ = lean_ctor_get(v_a_2727_, 1);
        lean_inc_ref(v_cont_2734_);
        lean_dec_ref(v_a_2727_);
        v___x_2735_ = lean_apply_2(v_cont_2734_, v_a_2728_, lean_box(0));
        v___x_2736_ = lean_unsigned_to_nat(0);
        v___x_2737_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_2736_,
            v_a_2729_,
            v___x_2735_,
            v___f_2730_,
        );
        return v___x_2737_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed(
    mut v_a_2738_: *mut LeanObject,
    mut v_a_2739_: *mut LeanObject,
    mut v_a_2740_: *mut LeanObject,
    mut v___f_2741_: *mut LeanObject,
    mut v_x_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_11067__boxed_2744_: u8 = 0;
    let mut v_res_2745_: *mut LeanObject = core::ptr::null_mut();
    v_a_11067__boxed_2744_ = (lean_unbox(v_a_2740_) as u8);
    v_res_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3(v_a_2738_, v_a_2739_, v_a_11067__boxed_2744_, v___f_2741_, v_x_2742_);
    return v_res_2745_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(
    mut v___x_2746_: *mut LeanObject,
    mut v_x_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2760_: u8 = 0;
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2766_: u8 = 0;
    let mut v_unused_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2747_) == 0 {
                    v_a_2749_ = lean_ctor_get(v_x_2747_, 0);
                    v_isSharedCheck_2757_ = (!lean_is_exclusive(v_x_2747_)) as u8;
                    if v_isSharedCheck_2757_ == 0 {
                        v___x_2751_ = v_x_2747_;
                        v_isShared_2752_ = v_isSharedCheck_2757_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2749_);
                        lean_dec(v_x_2747_);
                        v___x_2751_ = lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2757_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2766_ = (!lean_is_exclusive(v_x_2747_)) as u8;
                    if v_isSharedCheck_2766_ == 0 {
                        v_unused_2767_ = lean_ctor_get(v_x_2747_, 0);
                        lean_dec(v_unused_2767_);
                        v___x_2759_ = v_x_2747_;
                        v_isShared_2760_ = v_isSharedCheck_2766_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_2747_);
                        v___x_2759_ = lean_box(0);
                        v_isShared_2760_ = v_isSharedCheck_2766_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2755_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2755_, 0, v___x_2754_);
                return v___x_2755_;
            }
            3 => {
                v___x_2761_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2761_, 0, v___x_2746_);
                if v_isShared_2760_ == 0 {
                    lean_ctor_set(v___x_2759_, 0, v___x_2761_);
                    v___x_2763_ = v___x_2759_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2761_);
                    v___x_2763_ = v_reuseFailAlloc_2765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2764_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2764_, 0, v___x_2763_);
                return v___x_2764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0___boxed(
    mut v___x_2768_: *mut LeanObject,
    mut v_x_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2771_: *mut LeanObject = core::ptr::null_mut();
    v_res_2771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__0(v___x_2768_, v_x_2769_);
    return v_res_2771_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed(
    mut v_i_2774_: *mut LeanObject,
    mut v_a_2775_: *mut LeanObject,
    mut v_as_2776_: *mut LeanObject,
    mut v_sz_2777_: *mut LeanObject,
    mut v_x_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2780_: usize = 0;
    let mut v_a_11140__boxed_2781_: u8 = 0;
    let mut v_sz_boxed_2782_: usize = 0;
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2780_ = lean_unbox_usize(v_i_2774_);
    lean_dec(v_i_2774_);
    v_a_11140__boxed_2781_ = (lean_unbox(v_a_2775_) as u8);
    v_sz_boxed_2782_ = lean_unbox_usize(v_sz_2777_);
    lean_dec(v_sz_2777_);
    v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(v_i_boxed_2780_, v_a_11140__boxed_2781_, v_as_2776_, v_sz_boxed_2782_, v_x_2778_);
    return v_res_2783_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(
    mut v_a_2784_: u8,
    mut v_as_2785_: *mut LeanObject,
    mut v_sz_2786_: usize,
    mut v_i_2787_: usize,
    mut v_b_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2790_: u8 = 0;
    v___x_2790_ = lean_usize_dec_lt(v_i_2787_, v_sz_2786_);
    if v___x_2790_ == 0 {
        let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_2785_);
        v___x_2791_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2791_, 0, v_b_2788_);
        v___x_2792_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2792_, 0, v___x_2791_);
        return v___x_2792_;
    } else {
        let mut v_a_2793_: *mut LeanObject = core::ptr::null_mut();
        let mut v_selector_2794_: *mut LeanObject = core::ptr::null_mut();
        let mut v_unregisterFn_2795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2804_: u8 = 0;
        let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
        v_a_2793_ = lean_array_uget_borrowed(v_as_2785_, v_i_2787_);
        v_selector_2794_ = lean_ctor_get(v_a_2793_, 0);
        v_unregisterFn_2795_ = lean_ctor_get(v_selector_2794_, 2);
        lean_inc_ref(v_unregisterFn_2795_);
        v___x_2796_ = lean_apply_1(v_unregisterFn_2795_, lean_box(0));
        v___f_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0;
        v___x_2798_ = lean_unsigned_to_nat(0);
        v___x_2799_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_2798_,
            v_a_2784_,
            v___x_2796_,
            v___f_2797_,
        );
        v___x_2800_ = lean_box_usize(v_i_2787_);
        v___x_2801_ = lean_box((v_a_2784_) as usize);
        v___x_2802_ = lean_box_usize(v_sz_2786_);
        v___f_2803_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 4);
        lean_closure_set(v___f_2803_, 0, v___x_2800_);
        lean_closure_set(v___f_2803_, 1, v___x_2801_);
        lean_closure_set(v___f_2803_, 2, v_as_2785_);
        lean_closure_set(v___f_2803_, 3, v___x_2802_);
        v___x_2804_ = 0;
        v___x_2805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_2798_,
            v___x_2804_,
            v___x_2799_,
            v___f_2803_,
        );
        return v___x_2805_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___lam__1(
    mut v_i_2806_: usize,
    mut v_a_2807_: u8,
    mut v_as_2808_: *mut LeanObject,
    mut v_sz_2809_: usize,
    mut v_x_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_a_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v_a_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_a_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: usize = 0;
    let mut v___x_2838_: usize = 0;
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2810_) == 0 {
                    lean_dec_ref(v_as_2808_);
                    v_a_2812_ = lean_ctor_get(v_x_2810_, 0);
                    v_isSharedCheck_2820_ = (!lean_is_exclusive(v_x_2810_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v___x_2814_ = v_x_2810_;
                        v_isShared_2815_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2812_);
                        lean_dec(v_x_2810_);
                        v___x_2814_ = lean_box(0);
                        v_isShared_2815_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2821_ = lean_ctor_get(v_x_2810_, 0);
                    v_isSharedCheck_2840_ = (!lean_is_exclusive(v_x_2810_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2823_ = v_x_2810_;
                        v_isShared_2824_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2821_);
                        lean_dec(v_x_2810_);
                        v___x_2823_ = lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2815_ == 0 {
                    v___x_2817_ = v___x_2814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2812_);
                    v___x_2817_ = v_reuseFailAlloc_2819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2818_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2818_, 0, v___x_2817_);
                return v___x_2818_;
            }
            3 => {
                if lean_obj_tag(v_a_2821_) == 0 {
                    lean_dec_ref(v_as_2808_);
                    v_a_2825_ = lean_ctor_get(v_a_2821_, 0);
                    v_isSharedCheck_2835_ = (!lean_is_exclusive(v_a_2821_)) as u8;
                    if v_isSharedCheck_2835_ == 0 {
                        v___x_2827_ = v_a_2821_;
                        v_isShared_2828_ = v_isSharedCheck_2835_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2825_);
                        lean_dec(v_a_2821_);
                        v___x_2827_ = lean_box(0);
                        v_isShared_2828_ = v_isSharedCheck_2835_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2823_);
                    v_a_2836_ = lean_ctor_get(v_a_2821_, 0);
                    lean_inc(v_a_2836_);
                    lean_dec_ref_known(v_a_2821_, 1);
                    v___x_2837_ = 1usize;
                    v___x_2838_ = lean_usize_add(v_i_2806_, v___x_2837_);
                    v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_2807_, v_as_2808_, v_sz_2809_, v___x_2838_, v_a_2836_);
                    return v___x_2839_;
                }
            }
            4 => {
                if v_isShared_2824_ == 0 {
                    lean_ctor_set(v___x_2823_, 0, v_a_2825_);
                    v___x_2830_ = v___x_2823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2825_);
                    v___x_2830_ = v_reuseFailAlloc_2834_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2828_ == 0 {
                    lean_ctor_set(v___x_2827_, 0, v___x_2830_);
                    v___x_2832_ = v___x_2827_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
                    v___x_2832_ = v_reuseFailAlloc_2833_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___boxed(
    mut v_a_2841_: *mut LeanObject,
    mut v_as_2842_: *mut LeanObject,
    mut v_sz_2843_: *mut LeanObject,
    mut v_i_2844_: *mut LeanObject,
    mut v_b_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_11156__boxed_2847_: u8 = 0;
    let mut v_sz_boxed_2848_: usize = 0;
    let mut v_i_boxed_2849_: usize = 0;
    let mut v_res_2850_: *mut LeanObject = core::ptr::null_mut();
    v_a_11156__boxed_2847_ = (lean_unbox(v_a_2841_) as u8);
    v_sz_boxed_2848_ = lean_unbox_usize(v_sz_2843_);
    lean_dec(v_sz_2843_);
    v_i_boxed_2849_ = lean_unbox_usize(v_i_2844_);
    lean_dec(v_i_2844_);
    v_res_2850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_11156__boxed_2847_, v_as_2842_, v_sz_boxed_2848_, v_i_boxed_2849_, v_b_2845_);
    return v_res_2850_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(
    mut v___x_2851_: *mut LeanObject,
    mut v_a_2852_: u8,
    mut v___x_2853_: *mut LeanObject,
    mut v___f_2854_: *mut LeanObject,
    mut v_x_2855_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2855_) == 0 {
        let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_2854_);
        lean_dec_ref(v___x_2851_);
        v___x_2857_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2857_, 0, v_x_2855_);
        return v___x_2857_;
    } else {
        let mut v_sz_2858_: usize = 0;
        let mut v___x_2859_: usize = 0;
        let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_x_2855_, 1);
        v_sz_2858_ = lean_array_size(v___x_2851_);
        v___x_2859_ = 0usize;
        v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_2852_, v___x_2851_, v_sz_2858_, v___x_2859_, v___x_2853_);
        v___x_2861_ = lean_unsigned_to_nat(0);
        v___x_2862_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_2861_,
            v_a_2852_,
            v___x_2860_,
            v___f_2854_,
        );
        return v___x_2862_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed(
    mut v___x_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v___x_2865_: *mut LeanObject,
    mut v___f_2866_: *mut LeanObject,
    mut v_x_2867_: *mut LeanObject,
    mut v___y_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_11244__boxed_2869_: u8 = 0;
    let mut v_res_2870_: *mut LeanObject = core::ptr::null_mut();
    v_a_11244__boxed_2869_ = (lean_unbox(v_a_2864_) as u8);
    v_res_2870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5(v___x_2863_, v_a_11244__boxed_2869_, v___x_2865_, v___f_2866_, v_x_2867_);
    return v_res_2870_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: u8,
    mut v___f_2873_: *mut LeanObject,
    mut v___x_2874_: *mut LeanObject,
    mut v___x_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
    mut v___f_2877_: *mut LeanObject,
    mut v___f_2878_: *mut LeanObject,
    mut v_x_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2889_: u8 = 0;
    let mut v_a_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2879_) == 0 {
                    lean_dec_ref(v___f_2878_);
                    lean_dec_ref(v___f_2877_);
                    lean_dec_ref(v___x_2874_);
                    lean_dec_ref(v___f_2873_);
                    lean_dec_ref(v_a_2871_);
                    v_a_2881_ = lean_ctor_get(v_x_2879_, 0);
                    v_isSharedCheck_2889_ = (!lean_is_exclusive(v_x_2879_)) as u8;
                    if v_isSharedCheck_2889_ == 0 {
                        v___x_2883_ = v_x_2879_;
                        v_isShared_2884_ = v_isSharedCheck_2889_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2881_);
                        lean_dec(v_x_2879_);
                        v___x_2883_ = lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2889_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2890_ = lean_ctor_get(v_x_2879_, 0);
                    lean_inc(v_a_2890_);
                    lean_dec_ref_known(v_x_2879_, 1);
                    v___x_2891_ = lean_box((v_a_2872_) as usize);
                    v___f_2892_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 4);
                    lean_closure_set(v___f_2892_, 0, v_a_2871_);
                    lean_closure_set(v___f_2892_, 1, v_a_2890_);
                    lean_closure_set(v___f_2892_, 2, v___x_2891_);
                    lean_closure_set(v___f_2892_, 3, v___f_2873_);
                    v___x_2893_ = lean_box((v_a_2872_) as usize);
                    v___f_2894_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__5___boxed as *mut core::ffi::c_void, 6, 4);
                    lean_closure_set(v___f_2894_, 0, v___x_2874_);
                    lean_closure_set(v___f_2894_, 1, v___x_2893_);
                    lean_closure_set(v___f_2894_, 2, v___x_2875_);
                    lean_closure_set(v___f_2894_, 3, v___f_2892_);
                    v___x_2895_ = lean_io_promise_result_opt(v_a_2876_);
                    v___x_2896_ = lean_unsigned_to_nat(0);
                    v___x_2897_ = lean_task_map(v___f_2877_, v___x_2895_, v___x_2896_, v_a_2872_);
                    v___x_2898_ = lean_task_map(v___f_2878_, v___x_2897_, v___x_2896_, v_a_2872_);
                    v___x_2899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2899_, 0, v___x_2898_);
                    v___x_2900_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_2896_,
                            v_a_2872_,
                            v___x_2899_,
                            v___f_2894_,
                        );
                    return v___x_2900_;
                }
            }
            1 => {
                if v_isShared_2884_ == 0 {
                    v___x_2886_ = v___x_2883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2881_);
                    v___x_2886_ = v_reuseFailAlloc_2888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2887_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2887_, 0, v___x_2886_);
                return v___x_2887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed(
    mut v_a_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
    mut v___f_2903_: *mut LeanObject,
    mut v___x_2904_: *mut LeanObject,
    mut v___x_2905_: *mut LeanObject,
    mut v_a_2906_: *mut LeanObject,
    mut v___f_2907_: *mut LeanObject,
    mut v___f_2908_: *mut LeanObject,
    mut v_x_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_11273__boxed_2911_: u8 = 0;
    let mut v_res_2912_: *mut LeanObject = core::ptr::null_mut();
    v_a_11273__boxed_2911_ = (lean_unbox(v_a_2902_) as u8);
    v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6(v_a_2901_, v_a_11273__boxed_2911_, v___f_2903_, v___x_2904_, v___x_2905_, v_a_2906_, v___f_2907_, v___f_2908_, v_x_2909_);
    lean_dec(v_a_2906_);
    return v_res_2912_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(
    mut v___x_2913_: *mut LeanObject,
    mut v_a_2914_: u8,
    mut v___f_2915_: *mut LeanObject,
    mut v___f_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2935_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2939_: u8 = 0;
    let mut v_a_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2917_) == 0 {
                    lean_dec_ref(v___f_2916_);
                    lean_dec_ref(v___f_2915_);
                    v___x_2928_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2928_, 0, v___x_2913_);
                    v___x_2929_ = lean_task_pure(v___x_2928_);
                    return v___x_2929_;
                } else {
                    v_val_2930_ = lean_ctor_get(v_a_2917_, 0);
                    lean_inc(v_val_2930_);
                    lean_dec_ref_known(v_a_2917_, 1);
                    v___x_2931_ = l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(
                        v_val_2930_,
                    );
                    if lean_obj_tag(v___x_2931_) == 0 {
                        v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
                        v_isSharedCheck_2939_ = (!lean_is_exclusive(v___x_2931_)) as u8;
                        if v_isSharedCheck_2939_ == 0 {
                            v___x_2934_ = v___x_2931_;
                            v_isShared_2935_ = v_isSharedCheck_2939_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2932_);
                            lean_dec(v___x_2931_);
                            v___x_2934_ = lean_box(0);
                            v_isShared_2935_ = v_isSharedCheck_2939_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2940_ = lean_ctor_get(v___x_2931_, 0);
                        v_isSharedCheck_2947_ = (!lean_is_exclusive(v___x_2931_)) as u8;
                        if v_isSharedCheck_2947_ == 0 {
                            v___x_2942_ = v___x_2931_;
                            v_isShared_2943_ = v_isSharedCheck_2947_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2940_);
                            lean_dec(v___x_2931_);
                            v___x_2942_ = lean_box(0);
                            v_isShared_2943_ = v_isSharedCheck_2947_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2921_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2921_, 0, v_val_2920_);
                v___x_2922_ = lean_unsigned_to_nat(0);
                v___x_2923_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2922_,
                    v_a_2914_,
                    v___x_2921_,
                    v___f_2915_,
                );
                v___x_2924_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2922_,
                    v_a_2914_,
                    v___x_2923_,
                    v___f_2916_,
                );
                if lean_obj_tag(v___x_2924_) == 0 {
                    v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
                    lean_inc(v_a_2925_);
                    lean_dec_ref_known(v___x_2924_, 1);
                    v___x_2926_ = lean_task_pure(v_a_2925_);
                    return v___x_2926_;
                } else {
                    v_a_2927_ = lean_ctor_get(v___x_2924_, 0);
                    lean_inc_ref(v_a_2927_);
                    lean_dec_ref_known(v___x_2924_, 1);
                    return v_a_2927_;
                }
            }
            2 => {
                if v_isShared_2935_ == 0 {
                    lean_ctor_set_tag(v___x_2934_, 1);
                    v___x_2937_ = v___x_2934_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
                    v___x_2937_ = v_reuseFailAlloc_2938_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2920_ = v___x_2937_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2943_ == 0 {
                    lean_ctor_set_tag(v___x_2942_, 0);
                    v___x_2945_ = v___x_2942_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
                    v___x_2945_ = v_reuseFailAlloc_2946_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2920_ = v___x_2945_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed(
    mut v___x_2948_: *mut LeanObject,
    mut v_a_2949_: *mut LeanObject,
    mut v___f_2950_: *mut LeanObject,
    mut v___f_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_11341__boxed_2954_: u8 = 0;
    let mut v_res_2955_: *mut LeanObject = core::ptr::null_mut();
    v_a_11341__boxed_2954_ = (lean_unbox(v_a_2949_) as u8);
    v_res_2955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7(v___x_2948_, v_a_11341__boxed_2954_, v___f_2950_, v___f_2951_, v_a_2952_);
    return v_res_2955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(
    mut v_a_2956_: *mut LeanObject,
    mut v___f_2957_: *mut LeanObject,
    mut v___x_2958_: *mut LeanObject,
    mut v___x_2959_: *mut LeanObject,
    mut v_a_2960_: *mut LeanObject,
    mut v___f_2961_: *mut LeanObject,
    mut v___f_2962_: *mut LeanObject,
    mut v___f_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v___x_2965_: u8,
    mut v___f_2966_: *mut LeanObject,
    mut v_x_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut v_a_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2967_) == 0 {
                    lean_dec_ref(v___f_2966_);
                    lean_dec(v_a_2964_);
                    lean_dec_ref(v___f_2963_);
                    lean_dec_ref(v___f_2962_);
                    lean_dec_ref(v___f_2961_);
                    lean_dec(v_a_2960_);
                    lean_dec_ref(v___x_2958_);
                    lean_dec_ref(v___f_2957_);
                    lean_dec_ref(v_a_2956_);
                    v_a_2969_ = lean_ctor_get(v_x_2967_, 0);
                    v_isSharedCheck_2977_ = (!lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2977_ == 0 {
                        v___x_2971_ = v_x_2967_;
                        v_isShared_2972_ = v_isSharedCheck_2977_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2969_);
                        lean_dec(v_x_2967_);
                        v___x_2971_ = lean_box(0);
                        v_isShared_2972_ = v_isSharedCheck_2977_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2978_ = lean_ctor_get(v_x_2967_, 0);
                    v_isSharedCheck_3000_ = (!lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3000_ == 0 {
                        v___x_2980_ = v_x_2967_;
                        v_isShared_2981_ = v_isSharedCheck_3000_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2978_);
                        lean_dec(v_x_2967_);
                        v___x_2980_ = lean_box(0);
                        v_isShared_2981_ = v_isSharedCheck_3000_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2972_ == 0 {
                    v___x_2974_ = v___x_2971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2969_);
                    v___x_2974_ = v_reuseFailAlloc_2976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2975_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2975_, 0, v___x_2974_);
                return v___x_2975_;
            }
            3 => {
                v___x_2982_ = (lean_unbox(v_a_2978_) as u8);
                if v___x_2982_ == 0 {
                    v___x_2983_ = lean_io_promise_new();
                    lean_inc_n(v_a_2978_, 3);
                    lean_inc_ref(v_a_2956_);
                    v___f_2984_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__6___boxed as *mut core::ffi::c_void, 10, 8);
                    lean_closure_set(v___f_2984_, 0, v_a_2956_);
                    lean_closure_set(v___f_2984_, 1, v_a_2978_);
                    lean_closure_set(v___f_2984_, 2, v___f_2957_);
                    lean_closure_set(v___f_2984_, 3, v___x_2958_);
                    lean_closure_set(v___f_2984_, 4, v___x_2959_);
                    lean_closure_set(v___f_2984_, 5, v_a_2960_);
                    lean_closure_set(v___f_2984_, 6, v___f_2961_);
                    lean_closure_set(v___f_2984_, 7, v___f_2962_);
                    v___f_2985_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 4);
                    lean_closure_set(v___f_2985_, 0, v___x_2959_);
                    lean_closure_set(v___f_2985_, 1, v_a_2978_);
                    lean_closure_set(v___f_2985_, 2, v___f_2984_);
                    lean_closure_set(v___f_2985_, 3, v___f_2963_);
                    v___x_2986_ = lean_box((v___x_2965_) as usize);
                    v___f_2987_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__9___boxed as *mut core::ffi::c_void, 9, 7);
                    lean_closure_set(v___f_2987_, 0, v_a_2956_);
                    lean_closure_set(v___f_2987_, 1, v_a_2964_);
                    lean_closure_set(v___f_2987_, 2, v___f_2985_);
                    lean_closure_set(v___f_2987_, 3, v___x_2986_);
                    lean_closure_set(v___f_2987_, 4, v___x_2959_);
                    lean_closure_set(v___f_2987_, 5, v_a_2978_);
                    lean_closure_set(v___f_2987_, 6, v___f_2966_);
                    if v_isShared_2981_ == 0 {
                        lean_ctor_set(v___x_2980_, 0, v___x_2983_);
                        v___x_2989_ = v___x_2980_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2983_);
                        v___x_2989_ = v_reuseFailAlloc_2994_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2978_);
                    lean_dec_ref(v___f_2966_);
                    lean_dec(v_a_2964_);
                    lean_dec_ref(v___f_2963_);
                    lean_dec_ref(v___f_2962_);
                    lean_dec_ref(v___f_2961_);
                    lean_dec(v_a_2960_);
                    lean_dec_ref(v___x_2958_);
                    lean_dec_ref(v___f_2957_);
                    lean_dec_ref(v_a_2956_);
                    v___x_2995_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2995_, 0, v___x_2959_);
                    if v_isShared_2981_ == 0 {
                        lean_ctor_set(v___x_2980_, 0, v___x_2995_);
                        v___x_2997_ = v___x_2980_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2995_);
                        v___x_2997_ = v_reuseFailAlloc_2999_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2990_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2990_, 0, v___x_2989_);
                v___x_2991_ = lean_unsigned_to_nat(0);
                v___x_2992_ = (lean_unbox(v_a_2978_) as u8);
                lean_dec(v_a_2978_);
                v___x_2993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2991_,
                    v___x_2992_,
                    v___x_2990_,
                    v___f_2987_,
                );
                return v___x_2993_;
            }
            5 => {
                v___x_2998_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2998_, 0, v___x_2997_);
                return v___x_2998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed(
    mut v_a_3001_: *mut LeanObject,
    mut v___f_3002_: *mut LeanObject,
    mut v___x_3003_: *mut LeanObject,
    mut v___x_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
    mut v___f_3006_: *mut LeanObject,
    mut v___f_3007_: *mut LeanObject,
    mut v___f_3008_: *mut LeanObject,
    mut v_a_3009_: *mut LeanObject,
    mut v___x_3010_: *mut LeanObject,
    mut v___f_3011_: *mut LeanObject,
    mut v_x_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11421__boxed_3014_: u8 = 0;
    let mut v_res_3015_: *mut LeanObject = core::ptr::null_mut();
    v___x_11421__boxed_3014_ = (lean_unbox(v___x_3010_) as u8);
    v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10(v_a_3001_, v___f_3002_, v___x_3003_, v___x_3004_, v_a_3005_, v___f_3006_, v___f_3007_, v___f_3008_, v_a_3009_, v___x_11421__boxed_3014_, v___f_3011_, v_x_3012_);
    return v_res_3015_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed(
    mut v_i_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v___x_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_as_3024_: *mut LeanObject,
    mut v_sz_3025_: *mut LeanObject,
    mut v_x_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3028_: usize = 0;
    let mut v_sz_boxed_3029_: usize = 0;
    let mut v_res_3030_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3028_ = lean_unbox_usize(v_i_3019_);
    lean_dec(v_i_3019_);
    v_sz_boxed_3029_ = lean_unbox_usize(v_sz_3025_);
    lean_dec(v_sz_3025_);
    v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(v_i_boxed_3028_, v_a_3020_, v___x_3021_, v_a_3022_, v_a_3023_, v_as_3024_, v_sz_boxed_3029_, v_x_3026_);
    return v_res_3030_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(
    mut v_a_3031_: *mut LeanObject,
    mut v___x_3032_: *mut LeanObject,
    mut v_a_3033_: *mut LeanObject,
    mut v_a_3034_: *mut LeanObject,
    mut v_as_3035_: *mut LeanObject,
    mut v_sz_3036_: usize,
    mut v_i_3037_: usize,
    mut v_b_3038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3040_: u8 = 0;
    v___x_3040_ = lean_usize_dec_lt(v_i_3037_, v_sz_3036_);
    if v___x_3040_ == 0 {
        let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_3035_);
        lean_dec(v_a_3034_);
        lean_dec(v_a_3033_);
        lean_dec_ref(v___x_3032_);
        lean_dec(v_a_3031_);
        v___x_3041_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3041_, 0, v_b_3038_);
        v___x_3042_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3042_, 0, v___x_3041_);
        return v___x_3042_;
    } else {
        let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3049_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_3050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3056_: u8 = 0;
        let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
        v___x_3043_ = lean_st_ref_get(v_a_3034_);
        lean_inc_n(v_a_3031_, 2);
        v___f_3044_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
        lean_closure_set(v___f_3044_, 0, v_a_3031_);
        v___f_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__0;
        v___f_3046_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
        lean_closure_set(v___f_3046_, 0, v_a_3031_);
        v___x_3047_ = lean_box(0);
        v___f_3048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0;
        v___f_3049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___closed__1;
        v_a_3050_ = lean_array_uget_borrowed(v_as_3035_, v_i_3037_);
        v___x_3051_ = lean_box((v___x_3040_) as usize);
        lean_inc(v_a_3034_);
        lean_inc(v_a_3033_);
        lean_inc_ref(v___x_3032_);
        lean_inc(v_a_3050_);
        v___f_3052_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__10___boxed as *mut core::ffi::c_void, 13, 11);
        lean_closure_set(v___f_3052_, 0, v_a_3050_);
        lean_closure_set(v___f_3052_, 1, v___f_3044_);
        lean_closure_set(v___f_3052_, 2, v___x_3032_);
        lean_closure_set(v___f_3052_, 3, v___x_3047_);
        lean_closure_set(v___f_3052_, 4, v_a_3033_);
        lean_closure_set(v___f_3052_, 5, v___f_3045_);
        lean_closure_set(v___f_3052_, 6, v___f_3049_);
        lean_closure_set(v___f_3052_, 7, v___f_3046_);
        lean_closure_set(v___f_3052_, 8, v_a_3034_);
        lean_closure_set(v___f_3052_, 9, v___x_3051_);
        lean_closure_set(v___f_3052_, 10, v___f_3048_);
        v___x_3053_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3053_, 0, v___x_3043_);
        v___x_3054_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3054_, 0, v___x_3053_);
        v___x_3055_ = lean_unsigned_to_nat(0);
        v___x_3056_ = 0;
        v___x_3057_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3055_,
            v___x_3056_,
            v___x_3054_,
            v___f_3052_,
        );
        v___x_3058_ = lean_box_usize(v_i_3037_);
        v___x_3059_ = lean_box_usize(v_sz_3036_);
        v___f_3060_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11___boxed as *mut core::ffi::c_void, 9, 7);
        lean_closure_set(v___f_3060_, 0, v___x_3058_);
        lean_closure_set(v___f_3060_, 1, v_a_3031_);
        lean_closure_set(v___f_3060_, 2, v___x_3032_);
        lean_closure_set(v___f_3060_, 3, v_a_3033_);
        lean_closure_set(v___f_3060_, 4, v_a_3034_);
        lean_closure_set(v___f_3060_, 5, v_as_3035_);
        lean_closure_set(v___f_3060_, 6, v___x_3059_);
        v___x_3061_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3055_,
            v___x_3056_,
            v___x_3057_,
            v___f_3060_,
        );
        return v___x_3061_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___lam__11(
    mut v_i_3062_: usize,
    mut v_a_3063_: *mut LeanObject,
    mut v___x_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_as_3067_: *mut LeanObject,
    mut v_sz_3068_: usize,
    mut v_x_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v_a_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3083_: u8 = 0;
    let mut v_a_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3094_: u8 = 0;
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: usize = 0;
    let mut v___x_3097_: usize = 0;
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3069_) == 0 {
                    lean_dec_ref(v_as_3067_);
                    lean_dec(v_a_3066_);
                    lean_dec(v_a_3065_);
                    lean_dec_ref(v___x_3064_);
                    lean_dec(v_a_3063_);
                    v_a_3071_ = lean_ctor_get(v_x_3069_, 0);
                    v_isSharedCheck_3079_ = (!lean_is_exclusive(v_x_3069_)) as u8;
                    if v_isSharedCheck_3079_ == 0 {
                        v___x_3073_ = v_x_3069_;
                        v_isShared_3074_ = v_isSharedCheck_3079_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3071_);
                        lean_dec(v_x_3069_);
                        v___x_3073_ = lean_box(0);
                        v_isShared_3074_ = v_isSharedCheck_3079_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3080_ = lean_ctor_get(v_x_3069_, 0);
                    v_isSharedCheck_3099_ = (!lean_is_exclusive(v_x_3069_)) as u8;
                    if v_isSharedCheck_3099_ == 0 {
                        v___x_3082_ = v_x_3069_;
                        v_isShared_3083_ = v_isSharedCheck_3099_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3080_);
                        lean_dec(v_x_3069_);
                        v___x_3082_ = lean_box(0);
                        v_isShared_3083_ = v_isSharedCheck_3099_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3074_ == 0 {
                    v___x_3076_ = v___x_3073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3071_);
                    v___x_3076_ = v_reuseFailAlloc_3078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3077_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3077_, 0, v___x_3076_);
                return v___x_3077_;
            }
            3 => {
                if lean_obj_tag(v_a_3080_) == 0 {
                    lean_dec_ref(v_as_3067_);
                    lean_dec(v_a_3066_);
                    lean_dec(v_a_3065_);
                    lean_dec_ref(v___x_3064_);
                    lean_dec(v_a_3063_);
                    v_a_3084_ = lean_ctor_get(v_a_3080_, 0);
                    v_isSharedCheck_3094_ = (!lean_is_exclusive(v_a_3080_)) as u8;
                    if v_isSharedCheck_3094_ == 0 {
                        v___x_3086_ = v_a_3080_;
                        v_isShared_3087_ = v_isSharedCheck_3094_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3084_);
                        lean_dec(v_a_3080_);
                        v___x_3086_ = lean_box(0);
                        v_isShared_3087_ = v_isSharedCheck_3094_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3082_);
                    v_a_3095_ = lean_ctor_get(v_a_3080_, 0);
                    lean_inc(v_a_3095_);
                    lean_dec_ref_known(v_a_3080_, 1);
                    v___x_3096_ = 1usize;
                    v___x_3097_ = lean_usize_add(v_i_3062_, v___x_3096_);
                    v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_3063_, v___x_3064_, v_a_3065_, v_a_3066_, v_as_3067_, v_sz_3068_, v___x_3097_, v_a_3095_);
                    return v___x_3098_;
                }
            }
            4 => {
                if v_isShared_3083_ == 0 {
                    lean_ctor_set(v___x_3082_, 0, v_a_3084_);
                    v___x_3089_ = v___x_3082_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3084_);
                    v___x_3089_ = v_reuseFailAlloc_3093_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3087_ == 0 {
                    lean_ctor_set(v___x_3086_, 0, v___x_3089_);
                    v___x_3091_ = v___x_3086_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg___boxed(
    mut v_a_3100_: *mut LeanObject,
    mut v___x_3101_: *mut LeanObject,
    mut v_a_3102_: *mut LeanObject,
    mut v_a_3103_: *mut LeanObject,
    mut v_as_3104_: *mut LeanObject,
    mut v_sz_3105_: *mut LeanObject,
    mut v_i_3106_: *mut LeanObject,
    mut v_b_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3109_: usize = 0;
    let mut v_i_boxed_3110_: usize = 0;
    let mut v_res_3111_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3109_ = lean_unbox_usize(v_sz_3105_);
    lean_dec(v_sz_3105_);
    v_i_boxed_3110_ = lean_unbox_usize(v_i_3106_);
    lean_dec(v_i_3106_);
    v_res_3111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_3100_, v___x_3101_, v_a_3102_, v_a_3103_, v_as_3104_, v_sz_boxed_3109_, v_i_boxed_3110_, v_b_3107_);
    return v_res_3111_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__4(
    mut v___x_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
    mut v_a_3114_: *mut LeanObject,
    mut v___x_3115_: *mut LeanObject,
    mut v_x_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_a_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3128_: usize = 0;
    let mut v___x_3129_: usize = 0;
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3116_) == 0 {
                    lean_dec(v_a_3114_);
                    lean_dec(v_a_3113_);
                    lean_dec_ref(v___x_3112_);
                    v_a_3118_ = lean_ctor_get(v_x_3116_, 0);
                    v_isSharedCheck_3126_ = (!lean_is_exclusive(v_x_3116_)) as u8;
                    if v_isSharedCheck_3126_ == 0 {
                        v___x_3120_ = v_x_3116_;
                        v_isShared_3121_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3118_);
                        lean_dec(v_x_3116_);
                        v___x_3120_ = lean_box(0);
                        v_isShared_3121_ = v_isSharedCheck_3126_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3127_ = lean_ctor_get(v_x_3116_, 0);
                    v_sz_3128_ = lean_array_size(v___x_3112_);
                    v___x_3129_ = 0usize;
                    lean_inc(v_a_3113_);
                    lean_inc_ref(v___x_3112_);
                    lean_inc(v_a_3127_);
                    v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_3127_, v___x_3112_, v_a_3113_, v_a_3114_, v___x_3112_, v_sz_3128_, v___x_3129_, v___x_3115_);
                    v___f_3131_ = lean_alloc_closure(
                        l_Std_Async_Selectable_one___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3131_, 0, v_x_3116_);
                    v___f_3132_ = lean_alloc_closure(
                        l_Std_Async_Selectable_one___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_3132_, 0, v___x_3115_);
                    lean_closure_set(v___f_3132_, 1, v_a_3113_);
                    lean_closure_set(v___f_3132_, 2, v___f_3131_);
                    v___x_3133_ = lean_unsigned_to_nat(0);
                    v___x_3134_ = 0;
                    v___x_3135_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_3133_,
                            v___x_3134_,
                            v___x_3130_,
                            v___f_3132_,
                        );
                    return v___x_3135_;
                }
            }
            1 => {
                if v_isShared_3121_ == 0 {
                    v___x_3123_ = v___x_3120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3118_);
                    v___x_3123_ = v_reuseFailAlloc_3125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3124_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3124_, 0, v___x_3123_);
                return v___x_3124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__4___boxed(
    mut v___x_3136_: *mut LeanObject,
    mut v_a_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
    mut v___x_3139_: *mut LeanObject,
    mut v_x_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3142_: *mut LeanObject = core::ptr::null_mut();
    v_res_3142_ = l_Std_Async_Selectable_one___redArg___lam__4(
        v___x_3136_,
        v_a_3137_,
        v_a_3138_,
        v___x_3139_,
        v_x_3140_,
    );
    return v_res_3142_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__5(
    mut v___x_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v___x_3145_: *mut LeanObject,
    mut v_x_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_a_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3146_) == 0 {
                    lean_dec(v_a_3144_);
                    lean_dec_ref(v___x_3143_);
                    v_a_3148_ = lean_ctor_get(v_x_3146_, 0);
                    v_isSharedCheck_3156_ = (!lean_is_exclusive(v_x_3146_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v___x_3150_ = v_x_3146_;
                        v_isShared_3151_ = v_isSharedCheck_3156_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3148_);
                        lean_dec(v_x_3146_);
                        v___x_3150_ = lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3156_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3157_ = lean_ctor_get(v_x_3146_, 0);
                    v_isSharedCheck_3170_ = (!lean_is_exclusive(v_x_3146_)) as u8;
                    if v_isSharedCheck_3170_ == 0 {
                        v___x_3159_ = v_x_3146_;
                        v_isShared_3160_ = v_isSharedCheck_3170_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3157_);
                        lean_dec(v_x_3146_);
                        v___x_3159_ = lean_box(0);
                        v_isShared_3160_ = v_isSharedCheck_3170_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3151_ == 0 {
                    v___x_3153_ = v___x_3150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3148_);
                    v___x_3153_ = v_reuseFailAlloc_3155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3154_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3154_, 0, v___x_3153_);
                return v___x_3154_;
            }
            3 => {
                v___x_3161_ = lean_io_promise_new();
                v___f_3162_ = lean_alloc_closure(
                    l_Std_Async_Selectable_one___redArg___lam__4___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_3162_, 0, v___x_3143_);
                lean_closure_set(v___f_3162_, 1, v_a_3144_);
                lean_closure_set(v___f_3162_, 2, v_a_3157_);
                lean_closure_set(v___f_3162_, 3, v___x_3145_);
                if v_isShared_3160_ == 0 {
                    lean_ctor_set(v___x_3159_, 0, v___x_3161_);
                    v___x_3164_ = v___x_3159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3161_);
                    v___x_3164_ = v_reuseFailAlloc_3169_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3165_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3165_, 0, v___x_3164_);
                v___x_3166_ = lean_unsigned_to_nat(0);
                v___x_3167_ = 0;
                v___x_3168_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3166_,
                    v___x_3167_,
                    v___x_3165_,
                    v___f_3162_,
                );
                return v___x_3168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__5___boxed(
    mut v___x_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
    mut v___x_3173_: *mut LeanObject,
    mut v_x_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3176_: *mut LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Std_Async_Selectable_one___redArg___lam__5(
        v___x_3171_,
        v_a_3172_,
        v___x_3173_,
        v_x_3174_,
    );
    return v_res_3176_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__6(
    mut v___f_3177_: *mut LeanObject,
    mut v_x_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3183_: u8 = 0;
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3188_: u8 = 0;
    let mut v_a_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3192_: u8 = 0;
    let mut v_fst_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3178_) == 0 {
                    lean_dec_ref(v___f_3177_);
                    v_a_3180_ = lean_ctor_get(v_x_3178_, 0);
                    v_isSharedCheck_3188_ = (!lean_is_exclusive(v_x_3178_)) as u8;
                    if v_isSharedCheck_3188_ == 0 {
                        v___x_3182_ = v_x_3178_;
                        v_isShared_3183_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3180_);
                        lean_dec(v_x_3178_);
                        v___x_3182_ = lean_box(0);
                        v_isShared_3183_ = v_isSharedCheck_3188_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3189_ = lean_ctor_get(v_x_3178_, 0);
                    v_isSharedCheck_3214_ = (!lean_is_exclusive(v_x_3178_)) as u8;
                    if v_isSharedCheck_3214_ == 0 {
                        v___x_3191_ = v_x_3178_;
                        v_isShared_3192_ = v_isSharedCheck_3214_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3189_);
                        lean_dec(v_x_3178_);
                        v___x_3191_ = lean_box(0);
                        v_isShared_3192_ = v_isSharedCheck_3214_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3183_ == 0 {
                    v___x_3185_ = v___x_3182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3180_);
                    v___x_3185_ = v_reuseFailAlloc_3187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3186_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3186_, 0, v___x_3185_);
                return v___x_3186_;
            }
            3 => {
                v_fst_3193_ = lean_ctor_get(v_a_3189_, 0);
                lean_inc(v_fst_3193_);
                lean_dec(v_a_3189_);
                if lean_obj_tag(v_fst_3193_) == 0 {
                    v___x_3194_ = 0;
                    v___x_3195_ = lean_box((v___x_3194_) as usize);
                    v___x_3196_ = lean_st_mk_ref(v___x_3195_);
                    if v_isShared_3192_ == 0 {
                        lean_ctor_set(v___x_3191_, 0, v___x_3196_);
                        v___x_3198_ = v___x_3191_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3196_);
                        v___x_3198_ = v_reuseFailAlloc_3202_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_3177_);
                    v_val_3203_ = lean_ctor_get(v_fst_3193_, 0);
                    v_isSharedCheck_3213_ = (!lean_is_exclusive(v_fst_3193_)) as u8;
                    if v_isSharedCheck_3213_ == 0 {
                        v___x_3205_ = v_fst_3193_;
                        v_isShared_3206_ = v_isSharedCheck_3213_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_3203_);
                        lean_dec(v_fst_3193_);
                        v___x_3205_ = lean_box(0);
                        v_isShared_3206_ = v_isSharedCheck_3213_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3199_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3199_, 0, v___x_3198_);
                v___x_3200_ = lean_unsigned_to_nat(0);
                v___x_3201_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3200_,
                    v___x_3194_,
                    v___x_3199_,
                    v___f_3177_,
                );
                return v___x_3201_;
            }
            5 => {
                if v_isShared_3192_ == 0 {
                    lean_ctor_set(v___x_3191_, 0, v_val_3203_);
                    v___x_3208_ = v___x_3191_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_val_3203_);
                    v___x_3208_ = v_reuseFailAlloc_3212_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3206_ == 0 {
                    lean_ctor_set_tag(v___x_3205_, 0);
                    lean_ctor_set(v___x_3205_, 0, v___x_3208_);
                    v___x_3210_ = v___x_3205_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3208_);
                    v___x_3210_ = v_reuseFailAlloc_3211_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__6___boxed(
    mut v___f_3215_: *mut LeanObject,
    mut v_x_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3218_: *mut LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Std_Async_Selectable_one___redArg___lam__6(v___f_3215_, v_x_3216_);
    return v_res_3218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(
    mut v_a_3219_: *mut LeanObject,
    mut v___f_3220_: *mut LeanObject,
    mut v___x_3221_: *mut LeanObject,
    mut v_x_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3227_: u8 = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v_val_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cont_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3222_) == 0 {
                    lean_dec_ref(v___x_3221_);
                    lean_dec_ref(v___f_3220_);
                    lean_dec_ref(v_a_3219_);
                    v_a_3224_ = lean_ctor_get(v_x_3222_, 0);
                    v_isSharedCheck_3232_ = (!lean_is_exclusive(v_x_3222_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3226_ = v_x_3222_;
                        v_isShared_3227_ = v_isSharedCheck_3232_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3224_);
                        lean_dec(v_x_3222_);
                        v___x_3226_ = lean_box(0);
                        v_isShared_3227_ = v_isSharedCheck_3232_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3233_ = lean_ctor_get(v_x_3222_, 0);
                    v_isSharedCheck_3248_ = (!lean_is_exclusive(v_x_3222_)) as u8;
                    if v_isSharedCheck_3248_ == 0 {
                        v___x_3235_ = v_x_3222_;
                        v_isShared_3236_ = v_isSharedCheck_3248_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3233_);
                        lean_dec(v_x_3222_);
                        v___x_3235_ = lean_box(0);
                        v_isShared_3236_ = v_isSharedCheck_3248_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3227_ == 0 {
                    v___x_3229_ = v___x_3226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3224_);
                    v___x_3229_ = v_reuseFailAlloc_3231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3230_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3230_, 0, v___x_3229_);
                return v___x_3230_;
            }
            3 => {
                if lean_obj_tag(v_a_3233_) == 1 {
                    lean_del_object(v___x_3235_);
                    lean_dec_ref(v___x_3221_);
                    v_val_3237_ = lean_ctor_get(v_a_3233_, 0);
                    lean_inc(v_val_3237_);
                    lean_dec_ref_known(v_a_3233_, 1);
                    v_cont_3238_ = lean_ctor_get(v_a_3219_, 1);
                    lean_inc_ref(v_cont_3238_);
                    lean_dec_ref(v_a_3219_);
                    v___x_3239_ = lean_apply_2(v_cont_3238_, v_val_3237_, lean_box(0));
                    v___x_3240_ = lean_unsigned_to_nat(0);
                    v___x_3241_ = 0;
                    v___x_3242_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_3240_,
                            v___x_3241_,
                            v___x_3239_,
                            v___f_3220_,
                        );
                    return v___x_3242_;
                } else {
                    lean_dec(v_a_3233_);
                    lean_dec_ref(v___f_3220_);
                    lean_dec_ref(v_a_3219_);
                    v___x_3243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3243_, 0, v___x_3221_);
                    if v_isShared_3236_ == 0 {
                        lean_ctor_set(v___x_3235_, 0, v___x_3243_);
                        v___x_3245_ = v___x_3235_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3243_);
                        v___x_3245_ = v_reuseFailAlloc_3247_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3246_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3246_, 0, v___x_3245_);
                return v___x_3246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed(
    mut v_a_3249_: *mut LeanObject,
    mut v___f_3250_: *mut LeanObject,
    mut v___x_3251_: *mut LeanObject,
    mut v_x_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3254_: *mut LeanObject = core::ptr::null_mut();
    v_res_3254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1(v_a_3249_, v___f_3250_, v___x_3251_, v_x_3252_);
    return v_res_3254_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(
    mut v___x_3255_: *mut LeanObject,
    mut v_x_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3256_) == 0 {
                    v_a_3258_ = lean_ctor_get(v_x_3256_, 0);
                    v_isSharedCheck_3266_ = (!lean_is_exclusive(v_x_3256_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3260_ = v_x_3256_;
                        v_isShared_3261_ = v_isSharedCheck_3266_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3258_);
                        lean_dec(v_x_3256_);
                        v___x_3260_ = lean_box(0);
                        v_isShared_3261_ = v_isSharedCheck_3266_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3267_ = lean_ctor_get(v_x_3256_, 0);
                    v_isSharedCheck_3278_ = (!lean_is_exclusive(v_x_3256_)) as u8;
                    if v_isSharedCheck_3278_ == 0 {
                        v___x_3269_ = v_x_3256_;
                        v_isShared_3270_ = v_isSharedCheck_3278_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3267_);
                        lean_dec(v_x_3256_);
                        v___x_3269_ = lean_box(0);
                        v_isShared_3270_ = v_isSharedCheck_3278_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3264_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3264_, 0, v___x_3263_);
                return v___x_3264_;
            }
            3 => {
                v___x_3271_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3271_, 0, v_a_3267_);
                v___x_3272_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3272_, 0, v___x_3271_);
                lean_ctor_set(v___x_3272_, 1, v___x_3255_);
                v___x_3273_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3273_, 0, v___x_3272_);
                if v_isShared_3270_ == 0 {
                    lean_ctor_set(v___x_3269_, 0, v___x_3273_);
                    v___x_3275_ = v___x_3269_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3273_);
                    v___x_3275_ = v_reuseFailAlloc_3277_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3276_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                return v___x_3276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0___boxed(
    mut v___x_3279_: *mut LeanObject,
    mut v_x_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3282_: *mut LeanObject = core::ptr::null_mut();
    v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__0(v___x_3279_, v_x_3280_);
    return v_res_3282_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed(
    mut v_i_3288_: *mut LeanObject,
    mut v_as_3289_: *mut LeanObject,
    mut v_sz_3290_: *mut LeanObject,
    mut v_x_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3293_: usize = 0;
    let mut v_sz_boxed_3294_: usize = 0;
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3293_ = lean_unbox_usize(v_i_3288_);
    lean_dec(v_i_3288_);
    v_sz_boxed_3294_ = lean_unbox_usize(v_sz_3290_);
    lean_dec(v_sz_3290_);
    v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(v_i_boxed_3293_, v_as_3289_, v_sz_boxed_3294_, v_x_3291_);
    return v_res_3295_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(
    mut v_as_3296_: *mut LeanObject,
    mut v_sz_3297_: usize,
    mut v_i_3298_: usize,
    mut v_b_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3301_: u8 = 0;
    v___x_3301_ = lean_usize_dec_lt(v_i_3298_, v_sz_3297_);
    if v___x_3301_ == 0 {
        let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_3296_);
        v___x_3302_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3302_, 0, v_b_3299_);
        v___x_3303_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3303_, 0, v___x_3302_);
        return v___x_3303_;
    } else {
        let mut v_a_3304_: *mut LeanObject = core::ptr::null_mut();
        let mut v_selector_3305_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tryFn_3306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3312_: u8 = 0;
        let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_b_3299_);
        v_a_3304_ = lean_array_uget_borrowed(v_as_3296_, v_i_3298_);
        v_selector_3305_ = lean_ctor_get(v_a_3304_, 0);
        v_tryFn_3306_ = lean_ctor_get(v_selector_3305_, 0);
        lean_inc_ref(v_tryFn_3306_);
        v___x_3307_ = lean_apply_1(v_tryFn_3306_, lean_box(0));
        v___f_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__0;
        v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1;
        lean_inc(v_a_3304_);
        v___f_3310_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
        lean_closure_set(v___f_3310_, 0, v_a_3304_);
        lean_closure_set(v___f_3310_, 1, v___f_3308_);
        lean_closure_set(v___f_3310_, 2, v___x_3309_);
        v___x_3311_ = lean_unsigned_to_nat(0);
        v___x_3312_ = 0;
        v___x_3313_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3311_,
            v___x_3312_,
            v___x_3307_,
            v___f_3310_,
        );
        v___x_3314_ = lean_box_usize(v_i_3298_);
        v___x_3315_ = lean_box_usize(v_sz_3297_);
        v___f_3316_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 5, 3);
        lean_closure_set(v___f_3316_, 0, v___x_3314_);
        lean_closure_set(v___f_3316_, 1, v_as_3296_);
        lean_closure_set(v___f_3316_, 2, v___x_3315_);
        v___x_3317_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3311_,
            v___x_3312_,
            v___x_3313_,
            v___f_3316_,
        );
        return v___x_3317_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___lam__2(
    mut v_i_3318_: usize,
    mut v_as_3319_: *mut LeanObject,
    mut v_sz_3320_: usize,
    mut v_x_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_a_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3335_: u8 = 0;
    let mut v_a_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_a_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: usize = 0;
    let mut v___x_3349_: usize = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3321_) == 0 {
                    lean_dec_ref(v_as_3319_);
                    v_a_3323_ = lean_ctor_get(v_x_3321_, 0);
                    v_isSharedCheck_3331_ = (!lean_is_exclusive(v_x_3321_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v___x_3325_ = v_x_3321_;
                        v_isShared_3326_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3323_);
                        lean_dec(v_x_3321_);
                        v___x_3325_ = lean_box(0);
                        v_isShared_3326_ = v_isSharedCheck_3331_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3332_ = lean_ctor_get(v_x_3321_, 0);
                    v_isSharedCheck_3351_ = (!lean_is_exclusive(v_x_3321_)) as u8;
                    if v_isSharedCheck_3351_ == 0 {
                        v___x_3334_ = v_x_3321_;
                        v_isShared_3335_ = v_isSharedCheck_3351_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3332_);
                        lean_dec(v_x_3321_);
                        v___x_3334_ = lean_box(0);
                        v_isShared_3335_ = v_isSharedCheck_3351_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3326_ == 0 {
                    v___x_3328_ = v___x_3325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3323_);
                    v___x_3328_ = v_reuseFailAlloc_3330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3329_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3329_, 0, v___x_3328_);
                return v___x_3329_;
            }
            3 => {
                if lean_obj_tag(v_a_3332_) == 0 {
                    lean_dec_ref(v_as_3319_);
                    v_a_3336_ = lean_ctor_get(v_a_3332_, 0);
                    v_isSharedCheck_3346_ = (!lean_is_exclusive(v_a_3332_)) as u8;
                    if v_isSharedCheck_3346_ == 0 {
                        v___x_3338_ = v_a_3332_;
                        v_isShared_3339_ = v_isSharedCheck_3346_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3336_);
                        lean_dec(v_a_3332_);
                        v___x_3338_ = lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3346_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3334_);
                    v_a_3347_ = lean_ctor_get(v_a_3332_, 0);
                    lean_inc(v_a_3347_);
                    lean_dec_ref_known(v_a_3332_, 1);
                    v___x_3348_ = 1usize;
                    v___x_3349_ = lean_usize_add(v_i_3318_, v___x_3348_);
                    v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_3319_, v_sz_3320_, v___x_3349_, v_a_3347_);
                    return v___x_3350_;
                }
            }
            4 => {
                if v_isShared_3335_ == 0 {
                    lean_ctor_set(v___x_3334_, 0, v_a_3336_);
                    v___x_3341_ = v___x_3334_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3336_);
                    v___x_3341_ = v_reuseFailAlloc_3345_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3339_ == 0 {
                    lean_ctor_set(v___x_3338_, 0, v___x_3341_);
                    v___x_3343_ = v___x_3338_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___boxed(
    mut v_as_3352_: *mut LeanObject,
    mut v_sz_3353_: *mut LeanObject,
    mut v_i_3354_: *mut LeanObject,
    mut v_b_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3357_: usize = 0;
    let mut v_i_boxed_3358_: usize = 0;
    let mut v_res_3359_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3357_ = lean_unbox_usize(v_sz_3353_);
    lean_dec(v_sz_3353_);
    v_i_boxed_3358_ = lean_unbox_usize(v_i_3354_);
    lean_dec(v_i_3354_);
    v_res_3359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_3352_, v_sz_boxed_3357_, v_i_boxed_3358_, v_b_3355_);
    return v_res_3359_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__7(
    mut v___x_3360_: *mut LeanObject,
    mut v_x_3361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut v_a_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3375_: usize = 0;
    let mut v___x_3376_: usize = 0;
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3361_) == 0 {
                    lean_dec_ref(v___x_3360_);
                    v_a_3363_ = lean_ctor_get(v_x_3361_, 0);
                    v_isSharedCheck_3371_ = (!lean_is_exclusive(v_x_3361_)) as u8;
                    if v_isSharedCheck_3371_ == 0 {
                        v___x_3365_ = v_x_3361_;
                        v_isShared_3366_ = v_isSharedCheck_3371_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3363_);
                        lean_dec(v_x_3361_);
                        v___x_3365_ = lean_box(0);
                        v_isShared_3366_ = v_isSharedCheck_3371_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3372_ = lean_ctor_get(v_x_3361_, 0);
                    lean_inc(v_a_3372_);
                    lean_dec_ref_known(v_x_3361_, 1);
                    v___x_3373_ = lean_box(0);
                    v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg___closed__1;
                    v_sz_3375_ = lean_array_size(v___x_3360_);
                    v___x_3376_ = 0usize;
                    lean_inc_ref(v___x_3360_);
                    v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v___x_3360_, v_sz_3375_, v___x_3376_, v___x_3374_);
                    v___f_3378_ = lean_alloc_closure(
                        l_Std_Async_Selectable_one___redArg___lam__5___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_3378_, 0, v___x_3360_);
                    lean_closure_set(v___f_3378_, 1, v_a_3372_);
                    lean_closure_set(v___f_3378_, 2, v___x_3373_);
                    v___f_3379_ = lean_alloc_closure(
                        l_Std_Async_Selectable_one___redArg___lam__6___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3379_, 0, v___f_3378_);
                    v___x_3380_ = lean_unsigned_to_nat(0);
                    v___x_3381_ = 0;
                    v___x_3382_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_3380_,
                            v___x_3381_,
                            v___x_3377_,
                            v___f_3379_,
                        );
                    return v___x_3382_;
                }
            }
            1 => {
                if v_isShared_3366_ == 0 {
                    v___x_3368_ = v___x_3365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3363_);
                    v___x_3368_ = v_reuseFailAlloc_3370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3369_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3369_, 0, v___x_3368_);
                return v___x_3369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__7___boxed(
    mut v___x_3383_: *mut LeanObject,
    mut v_x_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3386_: *mut LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Std_Async_Selectable_one___redArg___lam__7(v___x_3383_, v_x_3384_);
    return v_res_3386_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__8(
    mut v_selectables_3387_: *mut LeanObject,
    mut v_x_3388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3393_: u8 = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut v_a_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: u64 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: u8 = 0;
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3388_) == 0 {
                    lean_dec_ref(v_selectables_3387_);
                    v_a_3390_ = lean_ctor_get(v_x_3388_, 0);
                    v_isSharedCheck_3398_ = (!lean_is_exclusive(v_x_3388_)) as u8;
                    if v_isSharedCheck_3398_ == 0 {
                        v___x_3392_ = v_x_3388_;
                        v_isShared_3393_ = v_isSharedCheck_3398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3390_);
                        lean_dec(v_x_3388_);
                        v___x_3392_ = lean_box(0);
                        v_isShared_3393_ = v_isSharedCheck_3398_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3399_ = lean_ctor_get(v_x_3388_, 0);
                    v_isSharedCheck_3416_ = (!lean_is_exclusive(v_x_3388_)) as u8;
                    if v_isSharedCheck_3416_ == 0 {
                        v___x_3401_ = v_x_3388_;
                        v_isShared_3402_ = v_isSharedCheck_3416_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3399_);
                        lean_dec(v_x_3388_);
                        v___x_3401_ = lean_box(0);
                        v_isShared_3402_ = v_isSharedCheck_3416_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3393_ == 0 {
                    v___x_3395_ = v___x_3392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3390_);
                    v___x_3395_ = v_reuseFailAlloc_3397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3396_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3396_, 0, v___x_3395_);
                return v___x_3396_;
            }
            3 => {
                v___x_3403_ = lean_io_promise_new();
                v___x_3404_ = l_ByteArray_toUInt64LE_x21(v_a_3399_);
                lean_dec(v_a_3399_);
                v___x_3405_ = lean_uint64_to_nat(v___x_3404_);
                v___x_3406_ = l_mkStdGen(v___x_3405_);
                lean_dec(v___x_3405_);
                v___x_3407_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(
                    v_selectables_3387_,
                    v___x_3406_,
                );
                v___f_3408_ = lean_alloc_closure(
                    l_Std_Async_Selectable_one___redArg___lam__7___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_3408_, 0, v___x_3407_);
                if v_isShared_3402_ == 0 {
                    lean_ctor_set(v___x_3401_, 0, v___x_3403_);
                    v___x_3410_ = v___x_3401_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3403_);
                    v___x_3410_ = v_reuseFailAlloc_3415_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3411_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3411_, 0, v___x_3410_);
                v___x_3412_ = lean_unsigned_to_nat(0);
                v___x_3413_ = 0;
                v___x_3414_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3412_,
                    v___x_3413_,
                    v___x_3411_,
                    v___f_3408_,
                );
                return v___x_3414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__8___boxed(
    mut v_selectables_3417_: *mut LeanObject,
    mut v_x_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3420_: *mut LeanObject = core::ptr::null_mut();
    v_res_3420_ = l_Std_Async_Selectable_one___redArg___lam__8(v_selectables_3417_, v_x_3418_);
    return v_res_3420_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__9(
    mut v___f_3421_: *mut LeanObject,
    mut v_____r_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: usize = 0;
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3435_: u8 = 0;
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut v_a_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3430_ = 8usize;
                v___x_3431_ = lean_io_get_random_bytes(v___x_3430_);
                if lean_obj_tag(v___x_3431_) == 0 {
                    v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
                    v_isSharedCheck_3439_ = (!lean_is_exclusive(v___x_3431_)) as u8;
                    if v_isSharedCheck_3439_ == 0 {
                        v___x_3434_ = v___x_3431_;
                        v_isShared_3435_ = v_isSharedCheck_3439_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3432_);
                        lean_dec(v___x_3431_);
                        v___x_3434_ = lean_box(0);
                        v_isShared_3435_ = v_isSharedCheck_3439_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3440_ = lean_ctor_get(v___x_3431_, 0);
                    v_isSharedCheck_3447_ = (!lean_is_exclusive(v___x_3431_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_3442_ = v___x_3431_;
                        v_isShared_3443_ = v_isSharedCheck_3447_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3440_);
                        lean_dec(v___x_3431_);
                        v___x_3442_ = lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3447_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3426_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3426_, 0, v_val_3425_);
                v___x_3427_ = lean_unsigned_to_nat(0);
                v___x_3428_ = 0;
                v___x_3429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3427_,
                    v___x_3428_,
                    v___x_3426_,
                    v___f_3421_,
                );
                return v___x_3429_;
            }
            2 => {
                if v_isShared_3435_ == 0 {
                    lean_ctor_set_tag(v___x_3434_, 1);
                    v___x_3437_ = v___x_3434_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
                    v___x_3437_ = v_reuseFailAlloc_3438_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_3425_ = v___x_3437_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3443_ == 0 {
                    lean_ctor_set_tag(v___x_3442_, 0);
                    v___x_3445_ = v___x_3442_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
                    v___x_3445_ = v_reuseFailAlloc_3446_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_3425_ = v___x_3445_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__9___boxed(
    mut v___f_3448_: *mut LeanObject,
    mut v_____r_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3451_: *mut LeanObject = core::ptr::null_mut();
    v_res_3451_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_3448_, v_____r_3449_);
    return v_res_3451_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__10(
    mut v___f_3452_: *mut LeanObject,
    mut v_x_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut v_a_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3453_) == 0 {
                    lean_dec_ref(v___f_3452_);
                    v_a_3455_ = lean_ctor_get(v_x_3453_, 0);
                    v_isSharedCheck_3463_ = (!lean_is_exclusive(v_x_3453_)) as u8;
                    if v_isSharedCheck_3463_ == 0 {
                        v___x_3457_ = v_x_3453_;
                        v_isShared_3458_ = v_isSharedCheck_3463_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3455_);
                        lean_dec(v_x_3453_);
                        v___x_3457_ = lean_box(0);
                        v_isShared_3458_ = v_isSharedCheck_3463_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3464_ = lean_ctor_get(v_x_3453_, 0);
                    lean_inc(v_a_3464_);
                    lean_dec_ref_known(v_x_3453_, 1);
                    v___x_3465_ = lean_apply_2(v___f_3452_, v_a_3464_, lean_box(0));
                    return v___x_3465_;
                }
            }
            1 => {
                if v_isShared_3458_ == 0 {
                    v___x_3460_ = v___x_3457_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3455_);
                    v___x_3460_ = v_reuseFailAlloc_3462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3461_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3461_, 0, v___x_3460_);
                return v___x_3461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___lam__10___boxed(
    mut v___f_3466_: *mut LeanObject,
    mut v_x_3467_: *mut LeanObject,
    mut v___y_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3469_: *mut LeanObject = core::ptr::null_mut();
    v_res_3469_ = l_Std_Async_Selectable_one___redArg___lam__10(v___f_3466_, v_x_3467_);
    return v_res_3469_;
}
pub unsafe fn l_Std_Async_Selectable_one___redArg(
    mut v_selectables_3477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    lean_inc_ref(v_selectables_3477_);
    v___f_3479_ = lean_alloc_closure(
        l_Std_Async_Selectable_one___redArg___lam__8___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3479_, 0, v_selectables_3477_);
    lean_inc_ref(v___f_3479_);
    v___f_3480_ = lean_alloc_closure(
        l_Std_Async_Selectable_one___redArg___lam__9___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3480_, 0, v___f_3479_);
    v___x_3481_ = lean_array_get_size(v_selectables_3477_);
    lean_dec_ref(v_selectables_3477_);
    v___x_3482_ = lean_unsigned_to_nat(0);
    v___x_3483_ = lean_nat_dec_eq(v___x_3481_, v___x_3482_);
    if v___x_3483_ == 0 {
        let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_3480_);
        v___x_3484_ = lean_box(0);
        v___x_3485_ = l_Std_Async_Selectable_one___redArg___lam__9(v___f_3479_, v___x_3484_);
        return v___x_3485_;
    } else {
        let mut v___f_3486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3488_: u8 = 0;
        let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_3479_);
        v___f_3486_ = lean_alloc_closure(
            l_Std_Async_Selectable_one___redArg___lam__10___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_3486_, 0, v___f_3480_);
        v___x_3487_ = l_Std_Async_Selectable_one___redArg___closed__3;
        v___x_3488_ = 0;
        v___x_3489_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3482_,
            v___x_3488_,
            v___x_3487_,
            v___f_3486_,
        );
        return v___x_3489_;
    }
}
pub unsafe fn l_Std_Async_Selectable_one___redArg___boxed(
    mut v_selectables_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3492_: *mut LeanObject = core::ptr::null_mut();
    v_res_3492_ = l_Std_Async_Selectable_one___redArg(v_selectables_3490_);
    return v_res_3492_;
}
pub unsafe fn l_Std_Async_Selectable_one(
    mut v_00_u03b1_3493_: *mut LeanObject,
    mut v_selectables_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    v___x_3496_ = l_Std_Async_Selectable_one___redArg(v_selectables_3494_);
    return v___x_3496_;
}
pub unsafe fn l_Std_Async_Selectable_one___boxed(
    mut v_00_u03b1_3497_: *mut LeanObject,
    mut v_selectables_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_Std_Async_Selectable_one(v_00_u03b1_3497_, v_selectables_3498_);
    return v_res_3500_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(
    mut v_00_u03b1_3501_: *mut LeanObject,
    mut v_a_3502_: u8,
    mut v_as_3503_: *mut LeanObject,
    mut v_sz_3504_: usize,
    mut v_i_3505_: usize,
    mut v_b_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg(v_a_3502_, v_as_3503_, v_sz_3504_, v_i_3505_, v_b_3506_);
    return v___x_3508_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___boxed(
    mut v_00_u03b1_3509_: *mut LeanObject,
    mut v_a_3510_: *mut LeanObject,
    mut v_as_3511_: *mut LeanObject,
    mut v_sz_3512_: *mut LeanObject,
    mut v_i_3513_: *mut LeanObject,
    mut v_b_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_12318__boxed_3516_: u8 = 0;
    let mut v_sz_boxed_3517_: usize = 0;
    let mut v_i_boxed_3518_: usize = 0;
    let mut v_res_3519_: *mut LeanObject = core::ptr::null_mut();
    v_a_12318__boxed_3516_ = (lean_unbox(v_a_3510_) as u8);
    v_sz_boxed_3517_ = lean_unbox_usize(v_sz_3512_);
    lean_dec(v_sz_3512_);
    v_i_boxed_3518_ = lean_unbox_usize(v_i_3513_);
    lean_dec(v_i_3513_);
    v_res_3519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0(v_00_u03b1_3509_, v_a_12318__boxed_3516_, v_as_3511_, v_sz_boxed_3517_, v_i_boxed_3518_, v_b_3514_);
    return v_res_3519_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(
    mut v_00_u03b1_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
    mut v___x_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_as_3525_: *mut LeanObject,
    mut v_sz_3526_: usize,
    mut v_i_3527_: usize,
    mut v_b_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___redArg(v_a_3521_, v___x_3522_, v_a_3523_, v_a_3524_, v_as_3525_, v_sz_3526_, v_i_3527_, v_b_3528_);
    return v___x_3530_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2___boxed(
    mut v_00_u03b1_3531_: *mut LeanObject,
    mut v_a_3532_: *mut LeanObject,
    mut v___x_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_as_3536_: *mut LeanObject,
    mut v_sz_3537_: *mut LeanObject,
    mut v_i_3538_: *mut LeanObject,
    mut v_b_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3541_: usize = 0;
    let mut v_i_boxed_3542_: usize = 0;
    let mut v_res_3543_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3541_ = lean_unbox_usize(v_sz_3537_);
    lean_dec(v_sz_3537_);
    v_i_boxed_3542_ = lean_unbox_usize(v_i_3538_);
    lean_dec(v_i_3538_);
    v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__2(v_00_u03b1_3531_, v_a_3532_, v___x_3533_, v_a_3534_, v_a_3535_, v_as_3536_, v_sz_boxed_3541_, v_i_boxed_3542_, v_b_3539_);
    return v_res_3543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(
    mut v_00_u03b1_3544_: *mut LeanObject,
    mut v_as_3545_: *mut LeanObject,
    mut v_sz_3546_: usize,
    mut v_i_3547_: usize,
    mut v_b_3548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___redArg(v_as_3545_, v_sz_3546_, v_i_3547_, v_b_3548_);
    return v___x_3550_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3___boxed(
    mut v_00_u03b1_3551_: *mut LeanObject,
    mut v_as_3552_: *mut LeanObject,
    mut v_sz_3553_: *mut LeanObject,
    mut v_i_3554_: *mut LeanObject,
    mut v_b_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3557_: usize = 0;
    let mut v_i_boxed_3558_: usize = 0;
    let mut v_res_3559_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3557_ = lean_unbox_usize(v_sz_3553_);
    lean_dec(v_sz_3553_);
    v_i_boxed_3558_ = lean_unbox_usize(v_i_3554_);
    lean_dec(v_i_3554_);
    v_res_3559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__3(v_00_u03b1_3551_, v_as_3552_, v_sz_boxed_3557_, v_i_boxed_3558_, v_b_3555_);
    return v_res_3559_;
}
pub unsafe fn l_Std_Async_Selectable_tryOne___redArg___lam__0(
    mut v_x_3564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3574_: u8 = 0;
    let mut v_a_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v_fst_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3584_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3564_) == 0 {
                    v_a_3566_ = lean_ctor_get(v_x_3564_, 0);
                    v_isSharedCheck_3574_ = (!lean_is_exclusive(v_x_3564_)) as u8;
                    if v_isSharedCheck_3574_ == 0 {
                        v___x_3568_ = v_x_3564_;
                        v_isShared_3569_ = v_isSharedCheck_3574_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3566_);
                        lean_dec(v_x_3564_);
                        v___x_3568_ = lean_box(0);
                        v_isShared_3569_ = v_isSharedCheck_3574_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3575_ = lean_ctor_get(v_x_3564_, 0);
                    v_isSharedCheck_3592_ = (!lean_is_exclusive(v_x_3564_)) as u8;
                    if v_isSharedCheck_3592_ == 0 {
                        v___x_3577_ = v_x_3564_;
                        v_isShared_3578_ = v_isSharedCheck_3592_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3575_);
                        lean_dec(v_x_3564_);
                        v___x_3577_ = lean_box(0);
                        v_isShared_3578_ = v_isSharedCheck_3592_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3569_ == 0 {
                    v___x_3571_ = v___x_3568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3566_);
                    v___x_3571_ = v_reuseFailAlloc_3573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3572_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3572_, 0, v___x_3571_);
                return v___x_3572_;
            }
            3 => {
                v_fst_3579_ = lean_ctor_get(v_a_3575_, 0);
                lean_inc(v_fst_3579_);
                lean_dec(v_a_3575_);
                if lean_obj_tag(v_fst_3579_) == 0 {
                    lean_del_object(v___x_3577_);
                    v___x_3580_ = l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1;
                    return v___x_3580_;
                } else {
                    v_val_3581_ = lean_ctor_get(v_fst_3579_, 0);
                    v_isSharedCheck_3591_ = (!lean_is_exclusive(v_fst_3579_)) as u8;
                    if v_isSharedCheck_3591_ == 0 {
                        v___x_3583_ = v_fst_3579_;
                        v_isShared_3584_ = v_isSharedCheck_3591_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_3581_);
                        lean_dec(v_fst_3579_);
                        v___x_3583_ = lean_box(0);
                        v_isShared_3584_ = v_isSharedCheck_3591_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3578_ == 0 {
                    lean_ctor_set(v___x_3577_, 0, v_val_3581_);
                    v___x_3586_ = v___x_3577_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_val_3581_);
                    v___x_3586_ = v_reuseFailAlloc_3590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3584_ == 0 {
                    lean_ctor_set_tag(v___x_3583_, 0);
                    lean_ctor_set(v___x_3583_, 0, v___x_3586_);
                    v___x_3588_ = v___x_3583_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
                    v___x_3588_ = v_reuseFailAlloc_3589_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_tryOne___redArg___lam__0___boxed(
    mut v_x_3593_: *mut LeanObject,
    mut v___y_3594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3595_: *mut LeanObject = core::ptr::null_mut();
    v_res_3595_ = l_Std_Async_Selectable_tryOne___redArg___lam__0(v_x_3593_);
    return v_res_3595_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(
    mut v___x_3596_: *mut LeanObject,
    mut v_x_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3602_: u8 = 0;
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3607_: u8 = 0;
    let mut v_a_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3597_) == 0 {
                    v_a_3599_ = lean_ctor_get(v_x_3597_, 0);
                    v_isSharedCheck_3607_ = (!lean_is_exclusive(v_x_3597_)) as u8;
                    if v_isSharedCheck_3607_ == 0 {
                        v___x_3601_ = v_x_3597_;
                        v_isShared_3602_ = v_isSharedCheck_3607_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3599_);
                        lean_dec(v_x_3597_);
                        v___x_3601_ = lean_box(0);
                        v_isShared_3602_ = v_isSharedCheck_3607_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3608_ = lean_ctor_get(v_x_3597_, 0);
                    v_isSharedCheck_3620_ = (!lean_is_exclusive(v_x_3597_)) as u8;
                    if v_isSharedCheck_3620_ == 0 {
                        v___x_3610_ = v_x_3597_;
                        v_isShared_3611_ = v_isSharedCheck_3620_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3608_);
                        lean_dec(v_x_3597_);
                        v___x_3610_ = lean_box(0);
                        v_isShared_3611_ = v_isSharedCheck_3620_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3602_ == 0 {
                    v___x_3604_ = v___x_3601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3599_);
                    v___x_3604_ = v_reuseFailAlloc_3606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3605_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3605_, 0, v___x_3604_);
                return v___x_3605_;
            }
            3 => {
                v___x_3612_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3612_, 0, v_a_3608_);
                v___x_3613_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3613_, 0, v___x_3612_);
                v___x_3614_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3614_, 0, v___x_3613_);
                lean_ctor_set(v___x_3614_, 1, v___x_3596_);
                v___x_3615_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3615_, 0, v___x_3614_);
                if v_isShared_3611_ == 0 {
                    lean_ctor_set(v___x_3610_, 0, v___x_3615_);
                    v___x_3617_ = v___x_3610_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3615_);
                    v___x_3617_ = v_reuseFailAlloc_3619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3618_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3618_, 0, v___x_3617_);
                return v___x_3618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0___boxed(
    mut v___x_3621_: *mut LeanObject,
    mut v_x_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3624_: *mut LeanObject = core::ptr::null_mut();
    v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__0(v___x_3621_, v_x_3622_);
    return v_res_3624_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(
    mut v_a_3625_: *mut LeanObject,
    mut v___x_3626_: *mut LeanObject,
    mut v___x_3627_: u8,
    mut v___f_3628_: *mut LeanObject,
    mut v___x_3629_: *mut LeanObject,
    mut v_x_3630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v_val_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cont_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3630_) == 0 {
                    lean_dec_ref(v___x_3629_);
                    lean_dec_ref(v___f_3628_);
                    lean_dec(v___x_3626_);
                    lean_dec_ref(v_a_3625_);
                    v_a_3632_ = lean_ctor_get(v_x_3630_, 0);
                    v_isSharedCheck_3640_ = (!lean_is_exclusive(v_x_3630_)) as u8;
                    if v_isSharedCheck_3640_ == 0 {
                        v___x_3634_ = v_x_3630_;
                        v_isShared_3635_ = v_isSharedCheck_3640_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3632_);
                        lean_dec(v_x_3630_);
                        v___x_3634_ = lean_box(0);
                        v_isShared_3635_ = v_isSharedCheck_3640_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3641_ = lean_ctor_get(v_x_3630_, 0);
                    v_isSharedCheck_3654_ = (!lean_is_exclusive(v_x_3630_)) as u8;
                    if v_isSharedCheck_3654_ == 0 {
                        v___x_3643_ = v_x_3630_;
                        v_isShared_3644_ = v_isSharedCheck_3654_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3641_);
                        lean_dec(v_x_3630_);
                        v___x_3643_ = lean_box(0);
                        v_isShared_3644_ = v_isSharedCheck_3654_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3635_ == 0 {
                    v___x_3637_ = v___x_3634_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3632_);
                    v___x_3637_ = v_reuseFailAlloc_3639_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3638_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3638_, 0, v___x_3637_);
                return v___x_3638_;
            }
            3 => {
                if lean_obj_tag(v_a_3641_) == 1 {
                    lean_del_object(v___x_3643_);
                    lean_dec_ref(v___x_3629_);
                    v_val_3645_ = lean_ctor_get(v_a_3641_, 0);
                    lean_inc(v_val_3645_);
                    lean_dec_ref_known(v_a_3641_, 1);
                    v_cont_3646_ = lean_ctor_get(v_a_3625_, 1);
                    lean_inc_ref(v_cont_3646_);
                    lean_dec_ref(v_a_3625_);
                    v___x_3647_ = lean_apply_2(v_cont_3646_, v_val_3645_, lean_box(0));
                    v___x_3648_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_3626_,
                            v___x_3627_,
                            v___x_3647_,
                            v___f_3628_,
                        );
                    return v___x_3648_;
                } else {
                    lean_dec(v_a_3641_);
                    lean_dec_ref(v___f_3628_);
                    lean_dec(v___x_3626_);
                    lean_dec_ref(v_a_3625_);
                    v___x_3649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3649_, 0, v___x_3629_);
                    if v_isShared_3644_ == 0 {
                        lean_ctor_set(v___x_3643_, 0, v___x_3649_);
                        v___x_3651_ = v___x_3643_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3649_);
                        v___x_3651_ = v_reuseFailAlloc_3653_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3652_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3652_, 0, v___x_3651_);
                return v___x_3652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed(
    mut v_a_3655_: *mut LeanObject,
    mut v___x_3656_: *mut LeanObject,
    mut v___x_3657_: *mut LeanObject,
    mut v___f_3658_: *mut LeanObject,
    mut v___x_3659_: *mut LeanObject,
    mut v_x_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2325__boxed_3662_: u8 = 0;
    let mut v_res_3663_: *mut LeanObject = core::ptr::null_mut();
    v___x_2325__boxed_3662_ = (lean_unbox(v___x_3657_) as u8);
    v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1(v_a_3655_, v___x_3656_, v___x_2325__boxed_3662_, v___f_3658_, v___x_3659_, v_x_3660_);
    return v_res_3663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed(
    mut v_i_3669_: *mut LeanObject,
    mut v___x_3670_: *mut LeanObject,
    mut v_as_3671_: *mut LeanObject,
    mut v_sz_3672_: *mut LeanObject,
    mut v_x_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3675_: usize = 0;
    let mut v_sz_boxed_3676_: usize = 0;
    let mut v_res_3677_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3675_ = lean_unbox_usize(v_i_3669_);
    lean_dec(v_i_3669_);
    v_sz_boxed_3676_ = lean_unbox_usize(v_sz_3672_);
    lean_dec(v_sz_3672_);
    v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(v_i_boxed_3675_, v___x_3670_, v_as_3671_, v_sz_boxed_3676_, v_x_3673_);
    return v_res_3677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(
    mut v___x_3678_: *mut LeanObject,
    mut v_as_3679_: *mut LeanObject,
    mut v_sz_3680_: usize,
    mut v_i_3681_: usize,
    mut v_b_3682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3684_: u8 = 0;
    v___x_3684_ = lean_usize_dec_lt(v_i_3681_, v_sz_3680_);
    if v___x_3684_ == 0 {
        let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_3679_);
        lean_dec(v___x_3678_);
        v___x_3685_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3685_, 0, v_b_3682_);
        v___x_3686_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3686_, 0, v___x_3685_);
        return v___x_3686_;
    } else {
        let mut v_a_3687_: *mut LeanObject = core::ptr::null_mut();
        let mut v_selector_3688_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tryFn_3689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3692_: u8 = 0;
        let mut v___f_3693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3701_: u8 = 0;
        let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_b_3682_);
        v_a_3687_ = lean_array_uget_borrowed(v_as_3679_, v_i_3681_);
        v_selector_3688_ = lean_ctor_get(v_a_3687_, 0);
        v_tryFn_3689_ = lean_ctor_get(v_selector_3688_, 0);
        lean_inc_ref(v_tryFn_3689_);
        v___x_3690_ = lean_apply_1(v_tryFn_3689_, lean_box(0));
        v___x_3691_ = lean_unsigned_to_nat(0);
        v___x_3692_ = lean_nat_dec_eq(v___x_3678_, v___x_3691_);
        v___f_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__0;
        v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1;
        v___x_3695_ = lean_box((v___x_3692_) as usize);
        lean_inc(v_a_3687_);
        v___f_3696_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 5);
        lean_closure_set(v___f_3696_, 0, v_a_3687_);
        lean_closure_set(v___f_3696_, 1, v___x_3691_);
        lean_closure_set(v___f_3696_, 2, v___x_3695_);
        lean_closure_set(v___f_3696_, 3, v___f_3693_);
        lean_closure_set(v___f_3696_, 4, v___x_3694_);
        v___x_3697_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3691_,
            v___x_3692_,
            v___x_3690_,
            v___f_3696_,
        );
        v___x_3698_ = lean_box_usize(v_i_3681_);
        v___x_3699_ = lean_box_usize(v_sz_3680_);
        v___f_3700_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 4);
        lean_closure_set(v___f_3700_, 0, v___x_3698_);
        lean_closure_set(v___f_3700_, 1, v___x_3678_);
        lean_closure_set(v___f_3700_, 2, v_as_3679_);
        lean_closure_set(v___f_3700_, 3, v___x_3699_);
        v___x_3701_ = 0;
        v___x_3702_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3691_,
            v___x_3701_,
            v___x_3697_,
            v___f_3700_,
        );
        return v___x_3702_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___lam__2(
    mut v_i_3703_: usize,
    mut v___x_3704_: *mut LeanObject,
    mut v_as_3705_: *mut LeanObject,
    mut v_sz_3706_: usize,
    mut v_x_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_a_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3721_: u8 = 0;
    let mut v_a_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut v_a_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: usize = 0;
    let mut v___x_3735_: usize = 0;
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3707_) == 0 {
                    lean_dec_ref(v_as_3705_);
                    lean_dec(v___x_3704_);
                    v_a_3709_ = lean_ctor_get(v_x_3707_, 0);
                    v_isSharedCheck_3717_ = (!lean_is_exclusive(v_x_3707_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3711_ = v_x_3707_;
                        v_isShared_3712_ = v_isSharedCheck_3717_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3709_);
                        lean_dec(v_x_3707_);
                        v___x_3711_ = lean_box(0);
                        v_isShared_3712_ = v_isSharedCheck_3717_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3718_ = lean_ctor_get(v_x_3707_, 0);
                    v_isSharedCheck_3737_ = (!lean_is_exclusive(v_x_3707_)) as u8;
                    if v_isSharedCheck_3737_ == 0 {
                        v___x_3720_ = v_x_3707_;
                        v_isShared_3721_ = v_isSharedCheck_3737_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3718_);
                        lean_dec(v_x_3707_);
                        v___x_3720_ = lean_box(0);
                        v_isShared_3721_ = v_isSharedCheck_3737_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3712_ == 0 {
                    v___x_3714_ = v___x_3711_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3715_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3715_, 0, v___x_3714_);
                return v___x_3715_;
            }
            3 => {
                if lean_obj_tag(v_a_3718_) == 0 {
                    lean_dec_ref(v_as_3705_);
                    lean_dec(v___x_3704_);
                    v_a_3722_ = lean_ctor_get(v_a_3718_, 0);
                    v_isSharedCheck_3732_ = (!lean_is_exclusive(v_a_3718_)) as u8;
                    if v_isSharedCheck_3732_ == 0 {
                        v___x_3724_ = v_a_3718_;
                        v_isShared_3725_ = v_isSharedCheck_3732_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3722_);
                        lean_dec(v_a_3718_);
                        v___x_3724_ = lean_box(0);
                        v_isShared_3725_ = v_isSharedCheck_3732_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3720_);
                    v_a_3733_ = lean_ctor_get(v_a_3718_, 0);
                    lean_inc(v_a_3733_);
                    lean_dec_ref_known(v_a_3718_, 1);
                    v___x_3734_ = 1usize;
                    v___x_3735_ = lean_usize_add(v_i_3703_, v___x_3734_);
                    v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_3704_, v_as_3705_, v_sz_3706_, v___x_3735_, v_a_3733_);
                    return v___x_3736_;
                }
            }
            4 => {
                if v_isShared_3721_ == 0 {
                    lean_ctor_set(v___x_3720_, 0, v_a_3722_);
                    v___x_3727_ = v___x_3720_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3722_);
                    v___x_3727_ = v_reuseFailAlloc_3731_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3725_ == 0 {
                    lean_ctor_set(v___x_3724_, 0, v___x_3727_);
                    v___x_3729_ = v___x_3724_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
                    v___x_3729_ = v_reuseFailAlloc_3730_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___boxed(
    mut v___x_3738_: *mut LeanObject,
    mut v_as_3739_: *mut LeanObject,
    mut v_sz_3740_: *mut LeanObject,
    mut v_i_3741_: *mut LeanObject,
    mut v_b_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3744_: usize = 0;
    let mut v_i_boxed_3745_: usize = 0;
    let mut v_res_3746_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3744_ = lean_unbox_usize(v_sz_3740_);
    lean_dec(v_sz_3740_);
    v_i_boxed_3745_ = lean_unbox_usize(v_i_3741_);
    lean_dec(v_i_3741_);
    v_res_3746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_3738_, v_as_3739_, v_sz_boxed_3744_, v_i_boxed_3745_, v_b_3742_);
    return v_res_3746_;
}
pub unsafe fn l_Std_Async_Selectable_tryOne___redArg___lam__1(
    mut v_selectables_3747_: *mut LeanObject,
    mut v___x_3748_: *mut LeanObject,
    mut v___x_3749_: *mut LeanObject,
    mut v___x_3750_: u8,
    mut v___f_3751_: *mut LeanObject,
    mut v_x_3752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_a_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: u64 = 0;
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3769_: usize = 0;
    let mut v___x_3770_: usize = 0;
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3752_) == 0 {
                    lean_dec_ref(v___f_3751_);
                    lean_dec(v___x_3749_);
                    lean_dec(v___x_3748_);
                    lean_dec_ref(v_selectables_3747_);
                    v_a_3754_ = lean_ctor_get(v_x_3752_, 0);
                    v_isSharedCheck_3762_ = (!lean_is_exclusive(v_x_3752_)) as u8;
                    if v_isSharedCheck_3762_ == 0 {
                        v___x_3756_ = v_x_3752_;
                        v_isShared_3757_ = v_isSharedCheck_3762_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3754_);
                        lean_dec(v_x_3752_);
                        v___x_3756_ = lean_box(0);
                        v_isShared_3757_ = v_isSharedCheck_3762_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3763_ = lean_ctor_get(v_x_3752_, 0);
                    lean_inc(v_a_3763_);
                    lean_dec_ref_known(v_x_3752_, 1);
                    v___x_3764_ = l_ByteArray_toUInt64LE_x21(v_a_3763_);
                    lean_dec(v_a_3763_);
                    v___x_3765_ = lean_uint64_to_nat(v___x_3764_);
                    v___x_3766_ = l_mkStdGen(v___x_3765_);
                    lean_dec(v___x_3765_);
                    v___x_3767_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(
                        v_selectables_3747_,
                        v___x_3766_,
                    );
                    v___x_3768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1;
                    v_sz_3769_ = lean_array_size(v___x_3767_);
                    v___x_3770_ = 0usize;
                    v___x_3771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_3748_, v___x_3767_, v_sz_3769_, v___x_3770_, v___x_3768_);
                    v___x_3772_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_3749_,
                            v___x_3750_,
                            v___x_3771_,
                            v___f_3751_,
                        );
                    return v___x_3772_;
                }
            }
            1 => {
                if v_isShared_3757_ == 0 {
                    v___x_3759_ = v___x_3756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3754_);
                    v___x_3759_ = v_reuseFailAlloc_3761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3760_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                return v___x_3760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed(
    mut v_selectables_3773_: *mut LeanObject,
    mut v___x_3774_: *mut LeanObject,
    mut v___x_3775_: *mut LeanObject,
    mut v___x_3776_: *mut LeanObject,
    mut v___f_3777_: *mut LeanObject,
    mut v_x_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2511__boxed_3780_: u8 = 0;
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v___x_2511__boxed_3780_ = (lean_unbox(v___x_3776_) as u8);
    v_res_3781_ = l_Std_Async_Selectable_tryOne___redArg___lam__1(
        v_selectables_3773_,
        v___x_3774_,
        v___x_3775_,
        v___x_2511__boxed_3780_,
        v___f_3777_,
        v_x_3778_,
    );
    return v_res_3781_;
}
pub unsafe fn l_Std_Async_Selectable_tryOne___redArg(
    mut v_selectables_3783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___f_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: usize = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3804_: u8 = 0;
    let mut v_a_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3785_ = lean_array_get_size(v_selectables_3783_);
                v___x_3786_ = lean_unsigned_to_nat(0);
                v___x_3787_ = lean_nat_dec_eq(v___x_3785_, v___x_3786_);
                if v___x_3787_ == 0 {
                    v___f_3788_ = l_Std_Async_Selectable_tryOne___redArg___closed__0;
                    v___x_3789_ = lean_box((v___x_3787_) as usize);
                    v___f_3790_ = lean_alloc_closure(
                        l_Std_Async_Selectable_tryOne___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        5,
                    );
                    lean_closure_set(v___f_3790_, 0, v_selectables_3783_);
                    lean_closure_set(v___f_3790_, 1, v___x_3785_);
                    lean_closure_set(v___f_3790_, 2, v___x_3786_);
                    lean_closure_set(v___f_3790_, 3, v___x_3789_);
                    lean_closure_set(v___f_3790_, 4, v___f_3788_);
                    v___x_3795_ = 8usize;
                    v___x_3796_ = lean_io_get_random_bytes(v___x_3795_);
                    if lean_obj_tag(v___x_3796_) == 0 {
                        v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
                        v_isSharedCheck_3804_ = (!lean_is_exclusive(v___x_3796_)) as u8;
                        if v_isSharedCheck_3804_ == 0 {
                            v___x_3799_ = v___x_3796_;
                            v_isShared_3800_ = v_isSharedCheck_3804_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3797_);
                            lean_dec(v___x_3796_);
                            v___x_3799_ = lean_box(0);
                            v_isShared_3800_ = v_isSharedCheck_3804_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3805_ = lean_ctor_get(v___x_3796_, 0);
                        v_isSharedCheck_3812_ = (!lean_is_exclusive(v___x_3796_)) as u8;
                        if v_isSharedCheck_3812_ == 0 {
                            v___x_3807_ = v___x_3796_;
                            v_isShared_3808_ = v_isSharedCheck_3812_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3805_);
                            lean_dec(v___x_3796_);
                            v___x_3807_ = lean_box(0);
                            v_isShared_3808_ = v_isSharedCheck_3812_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_selectables_3783_);
                    v___x_3813_ = l_Std_Async_Selectable_tryOne___redArg___lam__0___closed__1;
                    return v___x_3813_;
                }
            }
            1 => {
                v___x_3793_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3793_, 0, v_val_3792_);
                v___x_3794_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3786_,
                    v___x_3787_,
                    v___x_3793_,
                    v___f_3790_,
                );
                return v___x_3794_;
            }
            2 => {
                if v_isShared_3800_ == 0 {
                    lean_ctor_set_tag(v___x_3799_, 1);
                    v___x_3802_ = v___x_3799_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
                    v___x_3802_ = v_reuseFailAlloc_3803_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_3792_ = v___x_3802_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3808_ == 0 {
                    lean_ctor_set_tag(v___x_3807_, 0);
                    v___x_3810_ = v___x_3807_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
                    v___x_3810_ = v_reuseFailAlloc_3811_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_3792_ = v___x_3810_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_tryOne___redArg___boxed(
    mut v_selectables_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3816_: *mut LeanObject = core::ptr::null_mut();
    v_res_3816_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_3814_);
    return v_res_3816_;
}
pub unsafe fn l_Std_Async_Selectable_tryOne(
    mut v_00_u03b1_3817_: *mut LeanObject,
    mut v_selectables_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    v___x_3820_ = l_Std_Async_Selectable_tryOne___redArg(v_selectables_3818_);
    return v___x_3820_;
}
pub unsafe fn l_Std_Async_Selectable_tryOne___boxed(
    mut v_00_u03b1_3821_: *mut LeanObject,
    mut v_selectables_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3824_: *mut LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_Std_Async_Selectable_tryOne(v_00_u03b1_3821_, v_selectables_3822_);
    return v_res_3824_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(
    mut v_00_u03b1_3825_: *mut LeanObject,
    mut v___x_3826_: *mut LeanObject,
    mut v_as_3827_: *mut LeanObject,
    mut v_sz_3828_: usize,
    mut v_i_3829_: usize,
    mut v_b_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_3826_, v_as_3827_, v_sz_3828_, v_i_3829_, v_b_3830_);
    return v___x_3832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___boxed(
    mut v_00_u03b1_3833_: *mut LeanObject,
    mut v___x_3834_: *mut LeanObject,
    mut v_as_3835_: *mut LeanObject,
    mut v_sz_3836_: *mut LeanObject,
    mut v_i_3837_: *mut LeanObject,
    mut v_b_3838_: *mut LeanObject,
    mut v___y_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3840_: usize = 0;
    let mut v_i_boxed_3841_: usize = 0;
    let mut v_res_3842_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3840_ = lean_unbox_usize(v_sz_3836_);
    lean_dec(v_sz_3836_);
    v_i_boxed_3841_ = lean_unbox_usize(v_i_3837_);
    lean_dec(v_i_3837_);
    v_res_3842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0(v_00_u03b1_3833_, v___x_3834_, v_as_3835_, v_sz_boxed_3840_, v_i_boxed_3841_, v_b_3838_);
    return v_res_3842_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__1(
    mut v___x_3843_: *mut LeanObject,
    mut v_x_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v_unused_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3844_) == 0 {
                    v___x_3846_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3846_, 0, v_x_3844_);
                    return v___x_3846_;
                } else {
                    v_isSharedCheck_3854_ = (!lean_is_exclusive(v_x_3844_)) as u8;
                    if v_isSharedCheck_3854_ == 0 {
                        v_unused_3855_ = lean_ctor_get(v_x_3844_, 0);
                        lean_dec(v_unused_3855_);
                        v___x_3848_ = v_x_3844_;
                        v_isShared_3849_ = v_isSharedCheck_3854_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_3844_);
                        v___x_3848_ = lean_box(0);
                        v_isShared_3849_ = v_isSharedCheck_3854_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3849_ == 0 {
                    lean_ctor_set(v___x_3848_, 0, v___x_3843_);
                    v___x_3851_ = v___x_3848_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3843_);
                    v___x_3851_ = v_reuseFailAlloc_3853_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3852_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3852_, 0, v___x_3851_);
                return v___x_3852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__1___boxed(
    mut v___x_3856_: *mut LeanObject,
    mut v_x_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3859_: *mut LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Std_Async_Selectable_combine___redArg___lam__1(v___x_3856_, v_x_3857_);
    return v_res_3859_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__0(
    mut v_a_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    v___x_3861_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3861_, 0, v_a_3860_);
    return v___x_3861_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(
    mut v_a_3862_: *mut LeanObject,
    mut v___x_3863_: *mut LeanObject,
    mut v___x_3864_: u8,
    mut v___f_3865_: *mut LeanObject,
    mut v_x_3866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3871_: u8 = 0;
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3876_: u8 = 0;
    let mut v_a_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cont_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3866_) == 0 {
                    lean_dec_ref(v___f_3865_);
                    lean_dec(v___x_3863_);
                    lean_dec_ref(v_a_3862_);
                    v_a_3868_ = lean_ctor_get(v_x_3866_, 0);
                    v_isSharedCheck_3876_ = (!lean_is_exclusive(v_x_3866_)) as u8;
                    if v_isSharedCheck_3876_ == 0 {
                        v___x_3870_ = v_x_3866_;
                        v_isShared_3871_ = v_isSharedCheck_3876_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3868_);
                        lean_dec(v_x_3866_);
                        v___x_3870_ = lean_box(0);
                        v_isShared_3871_ = v_isSharedCheck_3876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3877_ = lean_ctor_get(v_x_3866_, 0);
                    lean_inc(v_a_3877_);
                    lean_dec_ref_known(v_x_3866_, 1);
                    v_cont_3878_ = lean_ctor_get(v_a_3862_, 1);
                    lean_inc_ref(v_cont_3878_);
                    lean_dec_ref(v_a_3862_);
                    v___x_3879_ = lean_apply_2(v_cont_3878_, v_a_3877_, lean_box(0));
                    v___x_3880_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_3863_,
                            v___x_3864_,
                            v___x_3879_,
                            v___f_3865_,
                        );
                    return v___x_3880_;
                }
            }
            1 => {
                if v_isShared_3871_ == 0 {
                    v___x_3873_ = v___x_3870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3868_);
                    v___x_3873_ = v_reuseFailAlloc_3875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3874_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3874_, 0, v___x_3873_);
                return v___x_3874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed(
    mut v_a_3881_: *mut LeanObject,
    mut v___x_3882_: *mut LeanObject,
    mut v___x_3883_: *mut LeanObject,
    mut v___f_3884_: *mut LeanObject,
    mut v_x_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7636__boxed_3887_: u8 = 0;
    let mut v_res_3888_: *mut LeanObject = core::ptr::null_mut();
    v___x_7636__boxed_3887_ = (lean_unbox(v___x_3883_) as u8);
    v_res_3888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3(v_a_3881_, v___x_3882_, v___x_7636__boxed_3887_, v___f_3884_, v_x_3885_);
    return v_res_3888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(
    mut v_promise_3889_: *mut LeanObject,
    mut v_x_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3890_) == 0 {
                    v_a_3892_ = lean_ctor_get(v_x_3890_, 0);
                    v_isSharedCheck_3902_ = (!lean_is_exclusive(v_x_3890_)) as u8;
                    if v_isSharedCheck_3902_ == 0 {
                        v___x_3894_ = v_x_3890_;
                        v_isShared_3895_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3892_);
                        lean_dec(v_x_3890_);
                        v___x_3894_ = lean_box(0);
                        v_isShared_3895_ = v_isSharedCheck_3902_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3903_, 0, v_x_3890_);
                    return v___x_3903_;
                }
            }
            1 => {
                if v_isShared_3895_ == 0 {
                    v___x_3897_ = v___x_3894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3892_);
                    v___x_3897_ = v_reuseFailAlloc_3901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3898_ = lean_io_promise_resolve(v___x_3897_, v_promise_3889_);
                v___x_3899_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3899_, 0, v___x_3898_);
                v___x_3900_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                return v___x_3900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed(
    mut v_promise_3904_: *mut LeanObject,
    mut v_x_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3907_: *mut LeanObject = core::ptr::null_mut();
    v_res_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2(v_promise_3904_, v_x_3905_);
    lean_dec(v_promise_3904_);
    return v_res_3907_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(
    mut v___x_3908_: *mut LeanObject,
    mut v___x_3909_: u8,
    mut v___f_3910_: *mut LeanObject,
    mut v___f_3911_: *mut LeanObject,
    mut v_val_3912_: *mut LeanObject,
    mut v_x_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_unused_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3913_) == 0 {
                    lean_dec_ref(v_val_3912_);
                    lean_dec_ref(v___f_3911_);
                    lean_dec_ref(v___f_3910_);
                    lean_dec(v___x_3908_);
                    v___x_3920_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3920_, 0, v_x_3913_);
                    return v___x_3920_;
                } else {
                    v_isSharedCheck_3933_ = (!lean_is_exclusive(v_x_3913_)) as u8;
                    if v_isSharedCheck_3933_ == 0 {
                        v_unused_3934_ = lean_ctor_get(v_x_3913_, 0);
                        lean_dec(v_unused_3934_);
                        v___x_3922_ = v_x_3913_;
                        v_isShared_3923_ = v_isSharedCheck_3933_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_x_3913_);
                        v___x_3922_ = lean_box(0);
                        v_isShared_3923_ = v_isSharedCheck_3933_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3917_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3917_, 0, v_val_3916_);
                lean_inc(v___x_3908_);
                v___x_3918_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3908_,
                    v___x_3909_,
                    v___x_3917_,
                    v___f_3910_,
                );
                v___x_3919_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3908_,
                    v___x_3909_,
                    v___x_3918_,
                    v___f_3911_,
                );
                return v___x_3919_;
            }
            2 => {
                v___x_3924_ =
                    l_IO_ofExcept___at___00Std_Async_Selectable_one_spec__1___redArg(v_val_3912_);
                if lean_obj_tag(v___x_3924_) == 0 {
                    v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
                    lean_inc(v_a_3925_);
                    lean_dec_ref_known(v___x_3924_, 1);
                    if v_isShared_3923_ == 0 {
                        lean_ctor_set(v___x_3922_, 0, v_a_3925_);
                        v___x_3927_ = v___x_3922_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3925_);
                        v___x_3927_ = v_reuseFailAlloc_3928_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3929_ = lean_ctor_get(v___x_3924_, 0);
                    lean_inc(v_a_3929_);
                    lean_dec_ref_known(v___x_3924_, 1);
                    if v_isShared_3923_ == 0 {
                        lean_ctor_set_tag(v___x_3922_, 0);
                        lean_ctor_set(v___x_3922_, 0, v_a_3929_);
                        v___x_3931_ = v___x_3922_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3929_);
                        v___x_3931_ = v_reuseFailAlloc_3932_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_val_3916_ = v___x_3927_;
                state = 1;
                continue;
            }
            4 => {
                v_val_3916_ = v___x_3931_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed(
    mut v___x_3935_: *mut LeanObject,
    mut v___x_3936_: *mut LeanObject,
    mut v___f_3937_: *mut LeanObject,
    mut v___f_3938_: *mut LeanObject,
    mut v_val_3939_: *mut LeanObject,
    mut v_x_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7706__boxed_3942_: u8 = 0;
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_7706__boxed_3942_ = (lean_unbox(v___x_3936_) as u8);
    v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4(v___x_3935_, v___x_7706__boxed_3942_, v___f_3937_, v___f_3938_, v_val_3939_, v_x_3940_);
    return v_res_3943_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed(
    mut v_i_3944_: *mut LeanObject,
    mut v___x_3945_: *mut LeanObject,
    mut v_as_3946_: *mut LeanObject,
    mut v_sz_3947_: *mut LeanObject,
    mut v_x_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3950_: usize = 0;
    let mut v_sz_boxed_3951_: usize = 0;
    let mut v_res_3952_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3950_ = lean_unbox_usize(v_i_3944_);
    lean_dec(v_i_3944_);
    v_sz_boxed_3951_ = lean_unbox_usize(v_sz_3947_);
    lean_dec(v_sz_3947_);
    v_res_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(v_i_boxed_3950_, v___x_3945_, v_as_3946_, v_sz_boxed_3951_, v_x_3948_);
    return v_res_3952_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(
    mut v___x_3953_: *mut LeanObject,
    mut v_as_3954_: *mut LeanObject,
    mut v_sz_3955_: usize,
    mut v_i_3956_: usize,
    mut v_b_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3959_: u8 = 0;
    v___x_3959_ = lean_usize_dec_lt(v_i_3956_, v_sz_3955_);
    if v___x_3959_ == 0 {
        let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_3954_);
        lean_dec(v___x_3953_);
        v___x_3960_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3960_, 0, v_b_3957_);
        v___x_3961_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3961_, 0, v___x_3960_);
        return v___x_3961_;
    } else {
        let mut v_a_3962_: *mut LeanObject = core::ptr::null_mut();
        let mut v_selector_3963_: *mut LeanObject = core::ptr::null_mut();
        let mut v_unregisterFn_3964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3967_: u8 = 0;
        let mut v___f_3968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3973_: u8 = 0;
        let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
        v_a_3962_ = lean_array_uget_borrowed(v_as_3954_, v_i_3956_);
        v_selector_3963_ = lean_ctor_get(v_a_3962_, 0);
        v_unregisterFn_3964_ = lean_ctor_get(v_selector_3963_, 2);
        lean_inc_ref(v_unregisterFn_3964_);
        v___x_3965_ = lean_apply_1(v_unregisterFn_3964_, lean_box(0));
        v___x_3966_ = lean_unsigned_to_nat(0);
        v___x_3967_ = lean_nat_dec_eq(v___x_3953_, v___x_3966_);
        v___f_3968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0;
        v___x_3969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3966_,
            v___x_3967_,
            v___x_3965_,
            v___f_3968_,
        );
        v___x_3970_ = lean_box_usize(v_i_3956_);
        v___x_3971_ = lean_box_usize(v_sz_3955_);
        v___f_3972_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 4);
        lean_closure_set(v___f_3972_, 0, v___x_3970_);
        lean_closure_set(v___f_3972_, 1, v___x_3953_);
        lean_closure_set(v___f_3972_, 2, v_as_3954_);
        lean_closure_set(v___f_3972_, 3, v___x_3971_);
        v___x_3973_ = 0;
        v___x_3974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3966_,
            v___x_3973_,
            v___x_3969_,
            v___f_3972_,
        );
        return v___x_3974_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___lam__1(
    mut v_i_3975_: usize,
    mut v___x_3976_: *mut LeanObject,
    mut v_as_3977_: *mut LeanObject,
    mut v_sz_3978_: usize,
    mut v_x_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3989_: u8 = 0;
    let mut v_a_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut v_a_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: usize = 0;
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3979_) == 0 {
                    lean_dec_ref(v_as_3977_);
                    lean_dec(v___x_3976_);
                    v_a_3981_ = lean_ctor_get(v_x_3979_, 0);
                    v_isSharedCheck_3989_ = (!lean_is_exclusive(v_x_3979_)) as u8;
                    if v_isSharedCheck_3989_ == 0 {
                        v___x_3983_ = v_x_3979_;
                        v_isShared_3984_ = v_isSharedCheck_3989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3981_);
                        lean_dec(v_x_3979_);
                        v___x_3983_ = lean_box(0);
                        v_isShared_3984_ = v_isSharedCheck_3989_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3990_ = lean_ctor_get(v_x_3979_, 0);
                    v_isSharedCheck_4009_ = (!lean_is_exclusive(v_x_3979_)) as u8;
                    if v_isSharedCheck_4009_ == 0 {
                        v___x_3992_ = v_x_3979_;
                        v_isShared_3993_ = v_isSharedCheck_4009_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3990_);
                        lean_dec(v_x_3979_);
                        v___x_3992_ = lean_box(0);
                        v_isShared_3993_ = v_isSharedCheck_4009_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3984_ == 0 {
                    v___x_3986_ = v___x_3983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3981_);
                    v___x_3986_ = v_reuseFailAlloc_3988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3987_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3987_, 0, v___x_3986_);
                return v___x_3987_;
            }
            3 => {
                if lean_obj_tag(v_a_3990_) == 0 {
                    lean_dec_ref(v_as_3977_);
                    lean_dec(v___x_3976_);
                    v_a_3994_ = lean_ctor_get(v_a_3990_, 0);
                    v_isSharedCheck_4004_ = (!lean_is_exclusive(v_a_3990_)) as u8;
                    if v_isSharedCheck_4004_ == 0 {
                        v___x_3996_ = v_a_3990_;
                        v_isShared_3997_ = v_isSharedCheck_4004_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3994_);
                        lean_dec(v_a_3990_);
                        v___x_3996_ = lean_box(0);
                        v_isShared_3997_ = v_isSharedCheck_4004_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3992_);
                    v_a_4005_ = lean_ctor_get(v_a_3990_, 0);
                    lean_inc(v_a_4005_);
                    lean_dec_ref_known(v_a_3990_, 1);
                    v___x_4006_ = 1usize;
                    v___x_4007_ = lean_usize_add(v_i_3975_, v___x_4006_);
                    v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_3976_, v_as_3977_, v_sz_3978_, v___x_4007_, v_a_4005_);
                    return v___x_4008_;
                }
            }
            4 => {
                if v_isShared_3993_ == 0 {
                    lean_ctor_set(v___x_3992_, 0, v_a_3994_);
                    v___x_3999_ = v___x_3992_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3994_);
                    v___x_3999_ = v_reuseFailAlloc_4003_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3997_ == 0 {
                    lean_ctor_set(v___x_3996_, 0, v___x_3999_);
                    v___x_4001_ = v___x_3996_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg___boxed(
    mut v___x_4010_: *mut LeanObject,
    mut v_as_4011_: *mut LeanObject,
    mut v_sz_4012_: *mut LeanObject,
    mut v_i_4013_: *mut LeanObject,
    mut v_b_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4016_: usize = 0;
    let mut v_i_boxed_4017_: usize = 0;
    let mut v_res_4018_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4016_ = lean_unbox_usize(v_sz_4012_);
    lean_dec(v_sz_4012_);
    v_i_boxed_4017_ = lean_unbox_usize(v_i_4013_);
    lean_dec(v_i_4013_);
    v_res_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_4010_, v_as_4011_, v_sz_boxed_4016_, v_i_boxed_4017_, v_b_4014_);
    return v_res_4018_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(
    mut v___x_4019_: *mut LeanObject,
    mut v___x_4020_: *mut LeanObject,
    mut v___x_4021_: *mut LeanObject,
    mut v___x_4022_: *mut LeanObject,
    mut v___x_4023_: u8,
    mut v___f_4024_: *mut LeanObject,
    mut v_x_4025_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4025_) == 0 {
        let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_4024_);
        lean_dec(v___x_4022_);
        lean_dec(v___x_4020_);
        lean_dec_ref(v___x_4019_);
        v___x_4027_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4027_, 0, v_x_4025_);
        return v___x_4027_;
    } else {
        let mut v_sz_4028_: usize = 0;
        let mut v___x_4029_: usize = 0;
        let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_x_4025_, 1);
        v_sz_4028_ = lean_array_size(v___x_4019_);
        v___x_4029_ = 0usize;
        v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_4020_, v___x_4019_, v_sz_4028_, v___x_4029_, v___x_4021_);
        v___x_4031_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_4022_,
            v___x_4023_,
            v___x_4030_,
            v___f_4024_,
        );
        return v___x_4031_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed(
    mut v___x_4032_: *mut LeanObject,
    mut v___x_4033_: *mut LeanObject,
    mut v___x_4034_: *mut LeanObject,
    mut v___x_4035_: *mut LeanObject,
    mut v___x_4036_: *mut LeanObject,
    mut v___f_4037_: *mut LeanObject,
    mut v_x_4038_: *mut LeanObject,
    mut v___y_4039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7874__boxed_4040_: u8 = 0;
    let mut v_res_4041_: *mut LeanObject = core::ptr::null_mut();
    v___x_7874__boxed_4040_ = (lean_unbox(v___x_4036_) as u8);
    v_res_4041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5(v___x_4032_, v___x_4033_, v___x_4034_, v___x_4035_, v___x_7874__boxed_4040_, v___f_4037_, v_x_4038_);
    return v_res_4041_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(
    mut v_promise_4042_: *mut LeanObject,
    mut v_x_4043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4043_) == 0 {
                    v_a_4045_ = lean_ctor_get(v_x_4043_, 0);
                    v_isSharedCheck_4053_ = (!lean_is_exclusive(v_x_4043_)) as u8;
                    if v_isSharedCheck_4053_ == 0 {
                        v___x_4047_ = v_x_4043_;
                        v_isShared_4048_ = v_isSharedCheck_4053_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4045_);
                        lean_dec(v_x_4043_);
                        v___x_4047_ = lean_box(0);
                        v_isShared_4048_ = v_isSharedCheck_4053_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4054_ = lean_io_promise_resolve(v_x_4043_, v_promise_4042_);
                    v___x_4055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4055_, 0, v___x_4054_);
                    v___x_4056_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4056_, 0, v___x_4055_);
                    return v___x_4056_;
                }
            }
            1 => {
                if v_isShared_4048_ == 0 {
                    v___x_4050_ = v___x_4047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4045_);
                    v___x_4050_ = v_reuseFailAlloc_4052_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4051_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4051_, 0, v___x_4050_);
                return v___x_4051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed(
    mut v_promise_4057_: *mut LeanObject,
    mut v_x_4058_: *mut LeanObject,
    mut v___y_4059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4060_: *mut LeanObject = core::ptr::null_mut();
    v_res_4060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1(v_promise_4057_, v_x_4058_);
    lean_dec(v_promise_4057_);
    return v_res_4060_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(
    mut v___x_4061_: *mut LeanObject,
    mut v_promise_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v___x_4064_: *mut LeanObject,
    mut v___x_4065_: u8,
    mut v___x_4066_: *mut LeanObject,
    mut v___x_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v___f_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v___f_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4070_) == 0 {
                    lean_dec_ref(v___f_4069_);
                    lean_dec(v___x_4067_);
                    lean_dec_ref(v___x_4066_);
                    lean_dec(v___x_4064_);
                    lean_dec_ref(v_a_4063_);
                    lean_dec(v_promise_4062_);
                    v___x_4072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4072_, 0, v___x_4061_);
                    v___x_4073_ = lean_task_pure(v___x_4072_);
                    return v___x_4073_;
                } else {
                    v_val_4074_ = lean_ctor_get(v_a_4070_, 0);
                    v_isSharedCheck_4095_ = (!lean_is_exclusive(v_a_4070_)) as u8;
                    if v_isSharedCheck_4095_ == 0 {
                        v___x_4076_ = v_a_4070_;
                        v_isShared_4077_ = v_isSharedCheck_4095_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4074_);
                        lean_dec(v_a_4070_);
                        v___x_4076_ = lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_promise_4062_);
                v___f_4078_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_4078_, 0, v_promise_4062_);
                v___f_4079_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_4079_, 0, v_promise_4062_);
                v___x_4080_ = lean_box((v___x_4065_) as usize);
                lean_inc_n(v___x_4064_, 4);
                v___f_4081_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 4);
                lean_closure_set(v___f_4081_, 0, v_a_4063_);
                lean_closure_set(v___f_4081_, 1, v___x_4064_);
                lean_closure_set(v___f_4081_, 2, v___x_4080_);
                lean_closure_set(v___f_4081_, 3, v___f_4079_);
                v___x_4082_ = lean_box((v___x_4065_) as usize);
                v___f_4083_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 5);
                lean_closure_set(v___f_4083_, 0, v___x_4064_);
                lean_closure_set(v___f_4083_, 1, v___x_4082_);
                lean_closure_set(v___f_4083_, 2, v___f_4081_);
                lean_closure_set(v___f_4083_, 3, v___f_4078_);
                lean_closure_set(v___f_4083_, 4, v_val_4074_);
                v___x_4084_ = lean_box((v___x_4065_) as usize);
                v___f_4085_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__5___boxed as *mut core::ffi::c_void, 8, 6);
                lean_closure_set(v___f_4085_, 0, v___x_4066_);
                lean_closure_set(v___f_4085_, 1, v___x_4067_);
                lean_closure_set(v___f_4085_, 2, v___x_4061_);
                lean_closure_set(v___f_4085_, 3, v___x_4064_);
                lean_closure_set(v___f_4085_, 4, v___x_4084_);
                lean_closure_set(v___f_4085_, 5, v___f_4083_);
                v___x_4086_ = l_IO_Promise_result_x21___redArg(v_a_4068_);
                v___x_4087_ = lean_task_map(v___f_4069_, v___x_4086_, v___x_4064_, v___x_4065_);
                if v_isShared_4077_ == 0 {
                    lean_ctor_set(v___x_4076_, 0, v___x_4087_);
                    v___x_4089_ = v___x_4076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4087_);
                    v___x_4089_ = v_reuseFailAlloc_4094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4090_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_4064_,
                    v___x_4065_,
                    v___x_4089_,
                    v___f_4085_,
                );
                if lean_obj_tag(v___x_4090_) == 0 {
                    v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
                    lean_inc(v_a_4091_);
                    lean_dec_ref_known(v___x_4090_, 1);
                    v___x_4092_ = lean_task_pure(v_a_4091_);
                    return v___x_4092_;
                } else {
                    v_a_4093_ = lean_ctor_get(v___x_4090_, 0);
                    lean_inc_ref(v_a_4093_);
                    lean_dec_ref_known(v___x_4090_, 1);
                    return v_a_4093_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed(
    mut v___x_4096_: *mut LeanObject,
    mut v_promise_4097_: *mut LeanObject,
    mut v_a_4098_: *mut LeanObject,
    mut v___x_4099_: *mut LeanObject,
    mut v___x_4100_: *mut LeanObject,
    mut v___x_4101_: *mut LeanObject,
    mut v___x_4102_: *mut LeanObject,
    mut v_a_4103_: *mut LeanObject,
    mut v___f_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7937__boxed_4107_: u8 = 0;
    let mut v_res_4108_: *mut LeanObject = core::ptr::null_mut();
    v___x_7937__boxed_4107_ = (lean_unbox(v___x_4100_) as u8);
    v_res_4108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6(v___x_4096_, v_promise_4097_, v_a_4098_, v___x_4099_, v___x_7937__boxed_4107_, v___x_4101_, v___x_4102_, v_a_4103_, v___f_4104_, v_a_4105_);
    lean_dec(v_a_4103_);
    return v_res_4108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(
    mut v___x_4109_: *mut LeanObject,
    mut v_promise_4110_: *mut LeanObject,
    mut v_a_4111_: *mut LeanObject,
    mut v___x_4112_: *mut LeanObject,
    mut v___x_4113_: u8,
    mut v___x_4114_: *mut LeanObject,
    mut v___x_4115_: *mut LeanObject,
    mut v___f_4116_: *mut LeanObject,
    mut v_a_4117_: *mut LeanObject,
    mut v___f_4118_: *mut LeanObject,
    mut v_x_4119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_a_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4119_) == 0 {
                    lean_dec_ref(v___f_4118_);
                    lean_dec_ref(v___f_4116_);
                    lean_dec(v___x_4115_);
                    lean_dec_ref(v___x_4114_);
                    lean_dec(v___x_4112_);
                    lean_dec_ref(v_a_4111_);
                    lean_dec(v_promise_4110_);
                    v_a_4121_ = lean_ctor_get(v_x_4119_, 0);
                    v_isSharedCheck_4129_ = (!lean_is_exclusive(v_x_4119_)) as u8;
                    if v_isSharedCheck_4129_ == 0 {
                        v___x_4123_ = v_x_4119_;
                        v_isShared_4124_ = v_isSharedCheck_4129_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4121_);
                        lean_dec(v_x_4119_);
                        v___x_4123_ = lean_box(0);
                        v_isShared_4124_ = v_isSharedCheck_4129_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4130_ = lean_ctor_get(v_x_4119_, 0);
                    v_isSharedCheck_4143_ = (!lean_is_exclusive(v_x_4119_)) as u8;
                    if v_isSharedCheck_4143_ == 0 {
                        v___x_4132_ = v_x_4119_;
                        v_isShared_4133_ = v_isSharedCheck_4143_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4130_);
                        lean_dec(v_x_4119_);
                        v___x_4132_ = lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4143_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4124_ == 0 {
                    v___x_4126_ = v___x_4123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4121_);
                    v___x_4126_ = v_reuseFailAlloc_4128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4127_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4127_, 0, v___x_4126_);
                return v___x_4127_;
            }
            3 => {
                v___x_4134_ = lean_box((v___x_4113_) as usize);
                lean_inc_n(v___x_4112_, 2);
                v___f_4135_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__6___boxed as *mut core::ffi::c_void, 11, 9);
                lean_closure_set(v___f_4135_, 0, v___x_4109_);
                lean_closure_set(v___f_4135_, 1, v_promise_4110_);
                lean_closure_set(v___f_4135_, 2, v_a_4111_);
                lean_closure_set(v___f_4135_, 3, v___x_4112_);
                lean_closure_set(v___f_4135_, 4, v___x_4134_);
                lean_closure_set(v___f_4135_, 5, v___x_4114_);
                lean_closure_set(v___f_4135_, 6, v___x_4115_);
                lean_closure_set(v___f_4135_, 7, v_a_4130_);
                lean_closure_set(v___f_4135_, 8, v___f_4116_);
                v___x_4136_ = lean_io_promise_result_opt(v_a_4117_);
                v___x_4137_ = lean_io_bind_task(v___x_4136_, v___f_4135_, v___x_4112_, v___x_4113_);
                lean_dec_ref(v___x_4137_);
                if v_isShared_4133_ == 0 {
                    lean_ctor_set(v___x_4132_, 0, v___x_4109_);
                    v___x_4139_ = v___x_4132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4109_);
                    v___x_4139_ = v_reuseFailAlloc_4142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4140_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4140_, 0, v___x_4139_);
                v___x_4141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_4112_,
                    v___x_4113_,
                    v___x_4140_,
                    v___f_4118_,
                );
                return v___x_4141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed(
    mut v___x_4144_: *mut LeanObject,
    mut v_promise_4145_: *mut LeanObject,
    mut v_a_4146_: *mut LeanObject,
    mut v___x_4147_: *mut LeanObject,
    mut v___x_4148_: *mut LeanObject,
    mut v___x_4149_: *mut LeanObject,
    mut v___x_4150_: *mut LeanObject,
    mut v___f_4151_: *mut LeanObject,
    mut v_a_4152_: *mut LeanObject,
    mut v___f_4153_: *mut LeanObject,
    mut v_x_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8009__boxed_4156_: u8 = 0;
    let mut v_res_4157_: *mut LeanObject = core::ptr::null_mut();
    v___x_8009__boxed_4156_ = (lean_unbox(v___x_4148_) as u8);
    v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7(v___x_4144_, v_promise_4145_, v_a_4146_, v___x_4147_, v___x_8009__boxed_4156_, v___x_4149_, v___x_4150_, v___f_4151_, v_a_4152_, v___f_4153_, v_x_4154_);
    lean_dec(v_a_4152_);
    return v_res_4157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(
    mut v___x_4158_: *mut LeanObject,
    mut v___x_4159_: u8,
    mut v___f_4160_: *mut LeanObject,
    mut v_x_4161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4166_: u8 = 0;
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4171_: u8 = 0;
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4174_: u8 = 0;
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_unused_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4161_) == 0 {
                    lean_dec_ref(v___f_4160_);
                    lean_dec(v___x_4158_);
                    v_a_4163_ = lean_ctor_get(v_x_4161_, 0);
                    v_isSharedCheck_4171_ = (!lean_is_exclusive(v_x_4161_)) as u8;
                    if v_isSharedCheck_4171_ == 0 {
                        v___x_4165_ = v_x_4161_;
                        v_isShared_4166_ = v_isSharedCheck_4171_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4163_);
                        lean_dec(v_x_4161_);
                        v___x_4165_ = lean_box(0);
                        v_isShared_4166_ = v_isSharedCheck_4171_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_4181_ = (!lean_is_exclusive(v_x_4161_)) as u8;
                    if v_isSharedCheck_4181_ == 0 {
                        v_unused_4182_ = lean_ctor_get(v_x_4161_, 0);
                        lean_dec(v_unused_4182_);
                        v___x_4173_ = v_x_4161_;
                        v_isShared_4174_ = v_isSharedCheck_4181_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_4161_);
                        v___x_4173_ = lean_box(0);
                        v_isShared_4174_ = v_isSharedCheck_4181_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4166_ == 0 {
                    v___x_4168_ = v___x_4165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4163_);
                    v___x_4168_ = v_reuseFailAlloc_4170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4169_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4169_, 0, v___x_4168_);
                return v___x_4169_;
            }
            3 => {
                v___x_4175_ = lean_io_promise_new();
                if v_isShared_4174_ == 0 {
                    lean_ctor_set(v___x_4173_, 0, v___x_4175_);
                    v___x_4177_ = v___x_4173_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4175_);
                    v___x_4177_ = v_reuseFailAlloc_4180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4178_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4178_, 0, v___x_4177_);
                v___x_4179_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_4158_,
                    v___x_4159_,
                    v___x_4178_,
                    v___f_4160_,
                );
                return v___x_4179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed(
    mut v___x_4183_: *mut LeanObject,
    mut v___x_4184_: *mut LeanObject,
    mut v___f_4185_: *mut LeanObject,
    mut v_x_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8084__boxed_4188_: u8 = 0;
    let mut v_res_4189_: *mut LeanObject = core::ptr::null_mut();
    v___x_8084__boxed_4188_ = (lean_unbox(v___x_4184_) as u8);
    v_res_4189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8(v___x_4183_, v___x_8084__boxed_4188_, v___f_4185_, v_x_4186_);
    return v_res_4189_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(
    mut v_waiter_4190_: *mut LeanObject,
    mut v_a_4191_: *mut LeanObject,
    mut v___x_4192_: *mut LeanObject,
    mut v___x_4193_: *mut LeanObject,
    mut v___x_4194_: u8,
    mut v___x_4195_: *mut LeanObject,
    mut v___x_4196_: *mut LeanObject,
    mut v___f_4197_: *mut LeanObject,
    mut v___f_4198_: *mut LeanObject,
    mut v_x_4199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4209_: u8 = 0;
    let mut v_selector_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v_registerFn_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4199_) == 0 {
                    lean_dec_ref(v___f_4198_);
                    lean_dec_ref(v___f_4197_);
                    lean_dec(v___x_4196_);
                    lean_dec_ref(v___x_4195_);
                    lean_dec(v___x_4193_);
                    lean_dec_ref(v_a_4191_);
                    lean_dec_ref(v_waiter_4190_);
                    v_a_4201_ = lean_ctor_get(v_x_4199_, 0);
                    v_isSharedCheck_4209_ = (!lean_is_exclusive(v_x_4199_)) as u8;
                    if v_isSharedCheck_4209_ == 0 {
                        v___x_4203_ = v_x_4199_;
                        v_isShared_4204_ = v_isSharedCheck_4209_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4201_);
                        lean_dec(v_x_4199_);
                        v___x_4203_ = lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4209_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_selector_4210_ = lean_ctor_get(v_a_4191_, 0);
                    v_a_4211_ = lean_ctor_get(v_x_4199_, 0);
                    lean_inc(v_a_4211_);
                    lean_dec_ref_known(v_x_4199_, 1);
                    v_finished_4212_ = lean_ctor_get(v_waiter_4190_, 0);
                    v_promise_4213_ = lean_ctor_get(v_waiter_4190_, 1);
                    v_isSharedCheck_4227_ = (!lean_is_exclusive(v_waiter_4190_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4215_ = v_waiter_4190_;
                        v_isShared_4216_ = v_isSharedCheck_4227_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_promise_4213_);
                        lean_inc(v_finished_4212_);
                        lean_dec(v_waiter_4190_);
                        v___x_4215_ = lean_box(0);
                        v_isShared_4216_ = v_isSharedCheck_4227_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4204_ == 0 {
                    v___x_4206_ = v___x_4203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4201_);
                    v___x_4206_ = v_reuseFailAlloc_4208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4207_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4207_, 0, v___x_4206_);
                return v___x_4207_;
            }
            3 => {
                v_registerFn_4217_ = lean_ctor_get(v_selector_4210_, 1);
                lean_inc(v_a_4211_);
                if v_isShared_4216_ == 0 {
                    lean_ctor_set(v___x_4215_, 1, v_a_4211_);
                    v___x_4219_ = v___x_4215_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_finished_4212_);
                    lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_a_4211_);
                    v___x_4219_ = v_reuseFailAlloc_4226_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v_registerFn_4217_);
                v___x_4220_ = lean_apply_2(v_registerFn_4217_, v___x_4219_, lean_box(0));
                v___x_4221_ = lean_box((v___x_4194_) as usize);
                lean_inc_n(v___x_4193_, 2);
                v___f_4222_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__7___boxed as *mut core::ffi::c_void, 12, 10);
                lean_closure_set(v___f_4222_, 0, v___x_4192_);
                lean_closure_set(v___f_4222_, 1, v_promise_4213_);
                lean_closure_set(v___f_4222_, 2, v_a_4191_);
                lean_closure_set(v___f_4222_, 3, v___x_4193_);
                lean_closure_set(v___f_4222_, 4, v___x_4221_);
                lean_closure_set(v___f_4222_, 5, v___x_4195_);
                lean_closure_set(v___f_4222_, 6, v___x_4196_);
                lean_closure_set(v___f_4222_, 7, v___f_4197_);
                lean_closure_set(v___f_4222_, 8, v_a_4211_);
                lean_closure_set(v___f_4222_, 9, v___f_4198_);
                v___x_4223_ = lean_box((v___x_4194_) as usize);
                v___f_4224_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__8___boxed as *mut core::ffi::c_void, 5, 3);
                lean_closure_set(v___f_4224_, 0, v___x_4193_);
                lean_closure_set(v___f_4224_, 1, v___x_4223_);
                lean_closure_set(v___f_4224_, 2, v___f_4222_);
                v___x_4225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_4193_,
                    v___x_4194_,
                    v___x_4220_,
                    v___f_4224_,
                );
                return v___x_4225_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed(
    mut v_waiter_4228_: *mut LeanObject,
    mut v_a_4229_: *mut LeanObject,
    mut v___x_4230_: *mut LeanObject,
    mut v___x_4231_: *mut LeanObject,
    mut v___x_4232_: *mut LeanObject,
    mut v___x_4233_: *mut LeanObject,
    mut v___x_4234_: *mut LeanObject,
    mut v___f_4235_: *mut LeanObject,
    mut v___f_4236_: *mut LeanObject,
    mut v_x_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8141__boxed_4239_: u8 = 0;
    let mut v_res_4240_: *mut LeanObject = core::ptr::null_mut();
    v___x_8141__boxed_4239_ = (lean_unbox(v___x_4232_) as u8);
    v_res_4240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9(v_waiter_4228_, v_a_4229_, v___x_4230_, v___x_4231_, v___x_8141__boxed_4239_, v___x_4233_, v___x_4234_, v___f_4235_, v___f_4236_, v_x_4237_);
    return v_res_4240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10___boxed(
    mut v_i_4242_: *mut LeanObject,
    mut v_waiter_4243_: *mut LeanObject,
    mut v___x_4244_: *mut LeanObject,
    mut v___x_4245_: *mut LeanObject,
    mut v_as_4246_: *mut LeanObject,
    mut v_sz_4247_: *mut LeanObject,
    mut v_x_4248_: *mut LeanObject,
    mut v___y_4249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4250_: usize = 0;
    let mut v_sz_boxed_4251_: usize = 0;
    let mut v_res_4252_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4250_ = lean_unbox_usize(v_i_4242_);
    lean_dec(v_i_4242_);
    v_sz_boxed_4251_ = lean_unbox_usize(v_sz_4247_);
    lean_dec(v_sz_4247_);
    v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10(v_i_boxed_4250_, v_waiter_4243_, v___x_4244_, v___x_4245_, v_as_4246_, v_sz_boxed_4251_, v_x_4248_);
    return v_res_4252_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(
    mut v_waiter_4253_: *mut LeanObject,
    mut v___x_4254_: *mut LeanObject,
    mut v___x_4255_: *mut LeanObject,
    mut v_as_4256_: *mut LeanObject,
    mut v_sz_4257_: usize,
    mut v_i_4258_: usize,
    mut v_b_4259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4261_: u8 = 0;
    v___x_4261_ = lean_usize_dec_lt(v_i_4258_, v_sz_4257_);
    if v___x_4261_ == 0 {
        let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_as_4256_);
        lean_dec_ref(v___x_4255_);
        lean_dec(v___x_4254_);
        lean_dec_ref(v_waiter_4253_);
        v___x_4262_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4262_, 0, v_b_4259_);
        v___x_4263_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4263_, 0, v___x_4262_);
        return v___x_4263_;
    } else {
        let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4269_: u8 = 0;
        let mut v_a_4270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4279_: u8 = 0;
        let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
        v___x_4264_ = lean_io_promise_new();
        v___f_4265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___closed__0;
        v___x_4266_ = lean_box(0);
        v___f_4267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_one_spec__0___redArg___closed__0;
        v___x_4268_ = lean_unsigned_to_nat(0);
        v___x_4269_ = lean_nat_dec_eq(v___x_4254_, v___x_4268_);
        v_a_4270_ = lean_array_uget_borrowed(v_as_4256_, v_i_4258_);
        v___x_4271_ = lean_box((v___x_4269_) as usize);
        lean_inc(v___x_4254_);
        lean_inc_ref(v___x_4255_);
        lean_inc(v_a_4270_);
        lean_inc_ref(v_waiter_4253_);
        v___f_4272_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__9___boxed as *mut core::ffi::c_void, 11, 9);
        lean_closure_set(v___f_4272_, 0, v_waiter_4253_);
        lean_closure_set(v___f_4272_, 1, v_a_4270_);
        lean_closure_set(v___f_4272_, 2, v___x_4266_);
        lean_closure_set(v___f_4272_, 3, v___x_4268_);
        lean_closure_set(v___f_4272_, 4, v___x_4271_);
        lean_closure_set(v___f_4272_, 5, v___x_4255_);
        lean_closure_set(v___f_4272_, 6, v___x_4254_);
        lean_closure_set(v___f_4272_, 7, v___f_4265_);
        lean_closure_set(v___f_4272_, 8, v___f_4267_);
        v___x_4273_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4273_, 0, v___x_4264_);
        v___x_4274_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4274_, 0, v___x_4273_);
        v___x_4275_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_4268_,
            v___x_4269_,
            v___x_4274_,
            v___f_4272_,
        );
        v___x_4276_ = lean_box_usize(v_i_4258_);
        v___x_4277_ = lean_box_usize(v_sz_4257_);
        v___f_4278_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10___boxed as *mut core::ffi::c_void, 8, 6);
        lean_closure_set(v___f_4278_, 0, v___x_4276_);
        lean_closure_set(v___f_4278_, 1, v_waiter_4253_);
        lean_closure_set(v___f_4278_, 2, v___x_4254_);
        lean_closure_set(v___f_4278_, 3, v___x_4255_);
        lean_closure_set(v___f_4278_, 4, v_as_4256_);
        lean_closure_set(v___f_4278_, 5, v___x_4277_);
        v___x_4279_ = 0;
        v___x_4280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_4268_,
            v___x_4279_,
            v___x_4275_,
            v___f_4278_,
        );
        return v___x_4280_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___lam__10(
    mut v_i_4281_: usize,
    mut v_waiter_4282_: *mut LeanObject,
    mut v___x_4283_: *mut LeanObject,
    mut v___x_4284_: *mut LeanObject,
    mut v_as_4285_: *mut LeanObject,
    mut v_sz_4286_: usize,
    mut v_x_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut v_a_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut v_a_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: usize = 0;
    let mut v___x_4315_: usize = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4287_) == 0 {
                    lean_dec_ref(v_as_4285_);
                    lean_dec_ref(v___x_4284_);
                    lean_dec(v___x_4283_);
                    lean_dec_ref(v_waiter_4282_);
                    v_a_4289_ = lean_ctor_get(v_x_4287_, 0);
                    v_isSharedCheck_4297_ = (!lean_is_exclusive(v_x_4287_)) as u8;
                    if v_isSharedCheck_4297_ == 0 {
                        v___x_4291_ = v_x_4287_;
                        v_isShared_4292_ = v_isSharedCheck_4297_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4289_);
                        lean_dec(v_x_4287_);
                        v___x_4291_ = lean_box(0);
                        v_isShared_4292_ = v_isSharedCheck_4297_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4298_ = lean_ctor_get(v_x_4287_, 0);
                    v_isSharedCheck_4317_ = (!lean_is_exclusive(v_x_4287_)) as u8;
                    if v_isSharedCheck_4317_ == 0 {
                        v___x_4300_ = v_x_4287_;
                        v_isShared_4301_ = v_isSharedCheck_4317_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4298_);
                        lean_dec(v_x_4287_);
                        v___x_4300_ = lean_box(0);
                        v_isShared_4301_ = v_isSharedCheck_4317_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4292_ == 0 {
                    v___x_4294_ = v___x_4291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4289_);
                    v___x_4294_ = v_reuseFailAlloc_4296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4295_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4295_, 0, v___x_4294_);
                return v___x_4295_;
            }
            3 => {
                if lean_obj_tag(v_a_4298_) == 0 {
                    lean_dec_ref(v_as_4285_);
                    lean_dec_ref(v___x_4284_);
                    lean_dec(v___x_4283_);
                    lean_dec_ref(v_waiter_4282_);
                    v_a_4302_ = lean_ctor_get(v_a_4298_, 0);
                    v_isSharedCheck_4312_ = (!lean_is_exclusive(v_a_4298_)) as u8;
                    if v_isSharedCheck_4312_ == 0 {
                        v___x_4304_ = v_a_4298_;
                        v_isShared_4305_ = v_isSharedCheck_4312_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4302_);
                        lean_dec(v_a_4298_);
                        v___x_4304_ = lean_box(0);
                        v_isShared_4305_ = v_isSharedCheck_4312_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4300_);
                    v_a_4313_ = lean_ctor_get(v_a_4298_, 0);
                    lean_inc(v_a_4313_);
                    lean_dec_ref_known(v_a_4298_, 1);
                    v___x_4314_ = 1usize;
                    v___x_4315_ = lean_usize_add(v_i_4281_, v___x_4314_);
                    v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_4282_, v___x_4283_, v___x_4284_, v_as_4285_, v_sz_4286_, v___x_4315_, v_a_4313_);
                    return v___x_4316_;
                }
            }
            4 => {
                if v_isShared_4301_ == 0 {
                    lean_ctor_set(v___x_4300_, 0, v_a_4302_);
                    v___x_4307_ = v___x_4300_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4302_);
                    v___x_4307_ = v_reuseFailAlloc_4311_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4305_ == 0 {
                    lean_ctor_set(v___x_4304_, 0, v___x_4307_);
                    v___x_4309_ = v___x_4304_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
                    v___x_4309_ = v_reuseFailAlloc_4310_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg___boxed(
    mut v_waiter_4318_: *mut LeanObject,
    mut v___x_4319_: *mut LeanObject,
    mut v___x_4320_: *mut LeanObject,
    mut v_as_4321_: *mut LeanObject,
    mut v_sz_4322_: *mut LeanObject,
    mut v_i_4323_: *mut LeanObject,
    mut v_b_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4326_: usize = 0;
    let mut v_i_boxed_4327_: usize = 0;
    let mut v_res_4328_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4326_ = lean_unbox_usize(v_sz_4322_);
    lean_dec(v_sz_4322_);
    v_i_boxed_4327_ = lean_unbox_usize(v_i_4323_);
    lean_dec(v_i_4323_);
    v_res_4328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_4318_, v___x_4319_, v___x_4320_, v_as_4321_, v_sz_boxed_4326_, v_i_boxed_4327_, v_b_4324_);
    return v_res_4328_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__0(
    mut v___x_4329_: *mut LeanObject,
    mut v___x_4330_: *mut LeanObject,
    mut v___x_4331_: *mut LeanObject,
    mut v___x_4332_: *mut LeanObject,
    mut v___x_4333_: u8,
    mut v___f_4334_: *mut LeanObject,
    mut v_waiter_4335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4337_: usize = 0;
    let mut v___x_4338_: usize = 0;
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4337_ = lean_array_size(v___x_4329_);
    v___x_4338_ = 0usize;
    lean_inc_ref(v___x_4329_);
    v___x_4339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_4335_, v___x_4330_, v___x_4329_, v___x_4329_, v_sz_4337_, v___x_4338_, v___x_4331_);
    v___x_4340_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4332_,
        v___x_4333_,
        v___x_4339_,
        v___f_4334_,
    );
    return v___x_4340_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__0___boxed(
    mut v___x_4341_: *mut LeanObject,
    mut v___x_4342_: *mut LeanObject,
    mut v___x_4343_: *mut LeanObject,
    mut v___x_4344_: *mut LeanObject,
    mut v___x_4345_: *mut LeanObject,
    mut v___f_4346_: *mut LeanObject,
    mut v_waiter_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8338__boxed_4349_: u8 = 0;
    let mut v_res_4350_: *mut LeanObject = core::ptr::null_mut();
    v___x_8338__boxed_4349_ = (lean_unbox(v___x_4345_) as u8);
    v_res_4350_ = l_Std_Async_Selectable_combine___redArg___lam__0(
        v___x_4341_,
        v___x_4342_,
        v___x_4343_,
        v___x_4344_,
        v___x_8338__boxed_4349_,
        v___f_4346_,
        v_waiter_4347_,
    );
    return v_res_4350_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__3(
    mut v___x_4351_: *mut LeanObject,
    mut v___x_4352_: *mut LeanObject,
    mut v_sz_4353_: usize,
    mut v___x_4354_: usize,
    mut v___x_4355_: *mut LeanObject,
    mut v___x_4356_: *mut LeanObject,
    mut v___x_4357_: u8,
    mut v___f_4358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_4351_, v___x_4352_, v_sz_4353_, v___x_4354_, v___x_4355_);
    v___x_4361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4356_,
        v___x_4357_,
        v___x_4360_,
        v___f_4358_,
    );
    return v___x_4361_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__3___boxed(
    mut v___x_4362_: *mut LeanObject,
    mut v___x_4363_: *mut LeanObject,
    mut v_sz_4364_: *mut LeanObject,
    mut v___x_4365_: *mut LeanObject,
    mut v___x_4366_: *mut LeanObject,
    mut v___x_4367_: *mut LeanObject,
    mut v___x_4368_: *mut LeanObject,
    mut v___f_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4371_: usize = 0;
    let mut v___x_8363__boxed_4372_: usize = 0;
    let mut v___x_8366__boxed_4373_: u8 = 0;
    let mut v_res_4374_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4371_ = lean_unbox_usize(v_sz_4364_);
    lean_dec(v_sz_4364_);
    v___x_8363__boxed_4372_ = lean_unbox_usize(v___x_4365_);
    lean_dec(v___x_4365_);
    v___x_8366__boxed_4373_ = (lean_unbox(v___x_4368_) as u8);
    v_res_4374_ = l_Std_Async_Selectable_combine___redArg___lam__3(
        v___x_4362_,
        v___x_4363_,
        v_sz_boxed_4371_,
        v___x_8363__boxed_4372_,
        v___x_4366_,
        v___x_4367_,
        v___x_8366__boxed_4373_,
        v___f_4369_,
    );
    return v_res_4374_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__2(
    mut v___x_4375_: *mut LeanObject,
    mut v___x_4376_: *mut LeanObject,
    mut v_sz_4377_: usize,
    mut v___x_4378_: usize,
    mut v___x_4379_: *mut LeanObject,
    mut v___x_4380_: *mut LeanObject,
    mut v___x_4381_: u8,
    mut v___f_4382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg(v___x_4375_, v___x_4376_, v_sz_4377_, v___x_4378_, v___x_4379_);
    v___x_4385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4380_,
        v___x_4381_,
        v___x_4384_,
        v___f_4382_,
    );
    return v___x_4385_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___lam__2___boxed(
    mut v___x_4386_: *mut LeanObject,
    mut v___x_4387_: *mut LeanObject,
    mut v_sz_4388_: *mut LeanObject,
    mut v___x_4389_: *mut LeanObject,
    mut v___x_4390_: *mut LeanObject,
    mut v___x_4391_: *mut LeanObject,
    mut v___x_4392_: *mut LeanObject,
    mut v___f_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4395_: usize = 0;
    let mut v___x_8391__boxed_4396_: usize = 0;
    let mut v___x_8394__boxed_4397_: u8 = 0;
    let mut v_res_4398_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4395_ = lean_unbox_usize(v_sz_4388_);
    lean_dec(v_sz_4388_);
    v___x_8391__boxed_4396_ = lean_unbox_usize(v___x_4389_);
    lean_dec(v___x_4389_);
    v___x_8394__boxed_4397_ = (lean_unbox(v___x_4392_) as u8);
    v_res_4398_ = l_Std_Async_Selectable_combine___redArg___lam__2(
        v___x_4386_,
        v___x_4387_,
        v_sz_boxed_4395_,
        v___x_8391__boxed_4396_,
        v___x_4390_,
        v___x_4391_,
        v___x_8394__boxed_4397_,
        v___f_4393_,
    );
    return v_res_4398_;
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg(
    mut v_selectables_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: usize = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4413_: u8 = 0;
    let mut v___f_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u64 = 0;
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4424_: usize = 0;
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut v_a_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4441_: u8 = 0;
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4405_ = lean_array_get_size(v_selectables_4403_);
                v___x_4406_ = lean_unsigned_to_nat(0);
                v___x_4407_ = lean_nat_dec_eq(v___x_4405_, v___x_4406_);
                if v___x_4407_ == 0 {
                    v___x_4408_ = 8usize;
                    v___x_4409_ = lean_io_get_random_bytes(v___x_4408_);
                    if lean_obj_tag(v___x_4409_) == 0 {
                        v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
                        v_isSharedCheck_4437_ = (!lean_is_exclusive(v___x_4409_)) as u8;
                        if v_isSharedCheck_4437_ == 0 {
                            v___x_4412_ = v___x_4409_;
                            v_isShared_4413_ = v_isSharedCheck_4437_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4410_);
                            lean_dec(v___x_4409_);
                            v___x_4412_ = lean_box(0);
                            v_isShared_4413_ = v_isSharedCheck_4437_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_selectables_4403_);
                        v_a_4438_ = lean_ctor_get(v___x_4409_, 0);
                        v_isSharedCheck_4445_ = (!lean_is_exclusive(v___x_4409_)) as u8;
                        if v_isSharedCheck_4445_ == 0 {
                            v___x_4440_ = v___x_4409_;
                            v_isShared_4441_ = v_isSharedCheck_4445_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4438_);
                            lean_dec(v___x_4409_);
                            v___x_4440_ = lean_box(0);
                            v_isShared_4441_ = v_isSharedCheck_4445_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_selectables_4403_);
                    v___x_4446_ = l_Std_Async_Selectable_one___redArg___closed__1;
                    v___x_4447_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4447_, 0, v___x_4446_);
                    return v___x_4447_;
                }
            }
            1 => {
                v___f_4414_ = l_Std_Async_Selectable_tryOne___redArg___closed__0;
                v___x_4415_ = l_ByteArray_toUInt64LE_x21(v_a_4410_);
                lean_dec(v_a_4410_);
                v___x_4416_ = lean_uint64_to_nat(v___x_4415_);
                v___x_4417_ = l_mkStdGen(v___x_4416_);
                lean_dec(v___x_4416_);
                v___x_4418_ = l___private_Std_Async_Select_0__Std_Async_shuffleIt___redArg(
                    v_selectables_4403_,
                    v___x_4417_,
                );
                v___x_4419_ = lean_box(0);
                v___f_4420_ = l_Std_Async_Selectable_combine___redArg___closed__0;
                v___x_4421_ = lean_box((v___x_4407_) as usize);
                lean_inc_ref_n(v___x_4418_, 2);
                v___f_4422_ = lean_alloc_closure(
                    l_Std_Async_Selectable_combine___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    6,
                );
                lean_closure_set(v___f_4422_, 0, v___x_4418_);
                lean_closure_set(v___f_4422_, 1, v___x_4405_);
                lean_closure_set(v___f_4422_, 2, v___x_4419_);
                lean_closure_set(v___f_4422_, 3, v___x_4406_);
                lean_closure_set(v___f_4422_, 4, v___x_4421_);
                lean_closure_set(v___f_4422_, 5, v___f_4420_);
                v___x_4423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_tryOne_spec__0___redArg___closed__1;
                v_sz_4424_ = lean_array_size(v___x_4418_);
                v___x_4425_ = lean_box_usize(v_sz_4424_);
                v___x_4426_ = l_Std_Async_Selectable_combine___redArg___boxed__const__1;
                v___x_4427_ = lean_box((v___x_4407_) as usize);
                v___f_4428_ = lean_alloc_closure(
                    l_Std_Async_Selectable_combine___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                lean_closure_set(v___f_4428_, 0, v___x_4405_);
                lean_closure_set(v___f_4428_, 1, v___x_4418_);
                lean_closure_set(v___f_4428_, 2, v___x_4425_);
                lean_closure_set(v___f_4428_, 3, v___x_4426_);
                lean_closure_set(v___f_4428_, 4, v___x_4419_);
                lean_closure_set(v___f_4428_, 5, v___x_4406_);
                lean_closure_set(v___f_4428_, 6, v___x_4427_);
                lean_closure_set(v___f_4428_, 7, v___f_4420_);
                v___x_4429_ = lean_box_usize(v_sz_4424_);
                v___x_4430_ = l_Std_Async_Selectable_combine___redArg___boxed__const__1;
                v___x_4431_ = lean_box((v___x_4407_) as usize);
                v___f_4432_ = lean_alloc_closure(
                    l_Std_Async_Selectable_combine___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                lean_closure_set(v___f_4432_, 0, v___x_4405_);
                lean_closure_set(v___f_4432_, 1, v___x_4418_);
                lean_closure_set(v___f_4432_, 2, v___x_4429_);
                lean_closure_set(v___f_4432_, 3, v___x_4430_);
                lean_closure_set(v___f_4432_, 4, v___x_4423_);
                lean_closure_set(v___f_4432_, 5, v___x_4406_);
                lean_closure_set(v___f_4432_, 6, v___x_4431_);
                lean_closure_set(v___f_4432_, 7, v___f_4414_);
                v___x_4433_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4433_, 0, v___f_4432_);
                lean_ctor_set(v___x_4433_, 1, v___f_4422_);
                lean_ctor_set(v___x_4433_, 2, v___f_4428_);
                if v_isShared_4413_ == 0 {
                    lean_ctor_set(v___x_4412_, 0, v___x_4433_);
                    v___x_4435_ = v___x_4412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4433_);
                    v___x_4435_ = v_reuseFailAlloc_4436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4435_;
            }
            3 => {
                if v_isShared_4441_ == 0 {
                    v___x_4443_ = v___x_4440_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
                    v___x_4443_ = v_reuseFailAlloc_4444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selectable_combine___redArg___boxed(
    mut v_selectables_4448_: *mut LeanObject,
    mut v_a_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4450_: *mut LeanObject = core::ptr::null_mut();
    v_res_4450_ = l_Std_Async_Selectable_combine___redArg(v_selectables_4448_);
    return v_res_4450_;
}
pub unsafe fn l_Std_Async_Selectable_combine(
    mut v_00_u03b1_4451_: *mut LeanObject,
    mut v_selectables_4452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    v___x_4454_ = l_Std_Async_Selectable_combine___redArg(v_selectables_4452_);
    return v___x_4454_;
}
pub unsafe fn l_Std_Async_Selectable_combine___boxed(
    mut v_00_u03b1_4455_: *mut LeanObject,
    mut v_selectables_4456_: *mut LeanObject,
    mut v_a_4457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4458_: *mut LeanObject = core::ptr::null_mut();
    v_res_4458_ = l_Std_Async_Selectable_combine(v_00_u03b1_4455_, v_selectables_4456_);
    return v_res_4458_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(
    mut v_00_u03b1_4459_: *mut LeanObject,
    mut v___x_4460_: *mut LeanObject,
    mut v_as_4461_: *mut LeanObject,
    mut v_sz_4462_: usize,
    mut v_i_4463_: usize,
    mut v_b_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___redArg(v___x_4460_, v_as_4461_, v_sz_4462_, v_i_4463_, v_b_4464_);
    return v___x_4466_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0___boxed(
    mut v_00_u03b1_4467_: *mut LeanObject,
    mut v___x_4468_: *mut LeanObject,
    mut v_as_4469_: *mut LeanObject,
    mut v_sz_4470_: *mut LeanObject,
    mut v_i_4471_: *mut LeanObject,
    mut v_b_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4474_: usize = 0;
    let mut v_i_boxed_4475_: usize = 0;
    let mut v_res_4476_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4474_ = lean_unbox_usize(v_sz_4470_);
    lean_dec(v_sz_4470_);
    v_i_boxed_4475_ = lean_unbox_usize(v_i_4471_);
    lean_dec(v_i_4471_);
    v_res_4476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__0(v_00_u03b1_4467_, v___x_4468_, v_as_4469_, v_sz_boxed_4474_, v_i_boxed_4475_, v_b_4472_);
    return v_res_4476_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(
    mut v_00_u03b1_4477_: *mut LeanObject,
    mut v_waiter_4478_: *mut LeanObject,
    mut v___x_4479_: *mut LeanObject,
    mut v___x_4480_: *mut LeanObject,
    mut v_as_4481_: *mut LeanObject,
    mut v_sz_4482_: usize,
    mut v_i_4483_: usize,
    mut v_b_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    v___x_4486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___redArg(v_waiter_4478_, v___x_4479_, v___x_4480_, v_as_4481_, v_sz_4482_, v_i_4483_, v_b_4484_);
    return v___x_4486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1___boxed(
    mut v_00_u03b1_4487_: *mut LeanObject,
    mut v_waiter_4488_: *mut LeanObject,
    mut v___x_4489_: *mut LeanObject,
    mut v___x_4490_: *mut LeanObject,
    mut v_as_4491_: *mut LeanObject,
    mut v_sz_4492_: *mut LeanObject,
    mut v_i_4493_: *mut LeanObject,
    mut v_b_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4496_: usize = 0;
    let mut v_i_boxed_4497_: usize = 0;
    let mut v_res_4498_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4496_ = lean_unbox_usize(v_sz_4492_);
    lean_dec(v_sz_4492_);
    v_i_boxed_4497_ = lean_unbox_usize(v_i_4493_);
    lean_dec(v_i_4493_);
    v_res_4498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Async_Selectable_combine_spec__1(v_00_u03b1_4487_, v_waiter_4488_, v___x_4489_, v___x_4490_, v_as_4491_, v_sz_boxed_4496_, v_i_boxed_4497_, v_b_4494_);
    return v_res_4498_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_Select(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Random(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Std_Async_Select(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_Select(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Random(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Async_Select(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Async_Select(builtin);
}
