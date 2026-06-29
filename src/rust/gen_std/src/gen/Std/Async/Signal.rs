// Lean compiler output
// Module: Std.Async.Signal
// Imports: Std.Time Std.Internal.UV.Signal Std.Async.Select
use crate::ffi::{
    lean_int32_of_nat, lean_io_as_task, lean_io_get_task_state, lean_io_map_task,
    lean_io_promise_resolve, lean_io_promise_result_opt, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_to_int, lean_st_ref_set, lean_st_ref_take, lean_task_bind, lean_task_map,
    lean_task_pure, lean_uv_signal_cancel, lean_uv_signal_mk, lean_uv_signal_next,
    lean_uv_signal_stop,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Std::Async::Basic::l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask;
use crate::r#gen::Std::Async::Select::{
    initialize_Std_Async_Select, runtime_initialize_Std_Async_Select,
};
use crate::r#gen::Std::Internal::UV::Signal::{
    initialize_Std_Internal_UV_Signal, runtime_initialize_Std_Internal_UV_Signal,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
pub static l_Std_Async_instReprSignal_repr___closed__0_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 104, 117, 112, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__2_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 105, 110, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__4_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 113, 117, 105, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__6_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 114, 97, 112, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__8_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 97, 98, 114, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__10_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 117, 115, 114, 49, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__12_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 117, 115, 114, 50, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__14_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 97, 108, 114, 109, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__16_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 101, 114, 109, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__18_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 99, 104, 108, 100, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__20_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 99, 111, 110, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__22_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 115, 116, 112, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__24_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 116, 105, 110, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__25_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__26_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 116, 111, 117, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__28_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 117, 114, 103, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__29_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__30_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 120, 99, 112, 117, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__31_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__32_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 120, 102, 115, 122, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__33_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__32_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__34_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 118, 116, 97, 108, 114, 109, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__35_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__34_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__36_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 112, 114, 111, 102, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__37_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__36_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__38_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 119, 105, 110, 99, 104, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__39_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__38_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__40_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 105, 111, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__41_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__40_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__42_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 115, 121, 115, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__43_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__42_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_instReprSignal_repr___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_instReprSignal_repr___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Async_instReprSignal_repr___closed__45_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_instReprSignal_repr___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_instReprSignal___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_instReprSignal_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_instReprSignal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_instReprSignal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_instBEqSignal___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_instBEqSignal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_instBEqSignal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instBEqSignal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_instBEqSignal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instBEqSignal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21: u32 = 0;
pub static l_Std_Async_Signal_Waiter_wait___closed__0_value: crate::leanh::LeanStringObject<49> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100,
            32, 116, 111, 32, 116, 104, 101, 32, 65, 115, 121, 110, 99, 32, 84, 97, 115, 107, 32,
            119, 97, 115, 32, 100, 114, 111, 112, 112, 101, 100, 0,
        ],
    };
static mut l_Std_Async_Signal_Waiter_wait___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_wait___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_wait___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Signal_Waiter_wait___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Signal_Waiter_wait___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_Signal_Waiter_wait___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_wait___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value:
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
static mut l_Std_Async_Signal_Waiter_selector___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value:
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
static mut l_Std_Async_Signal_Waiter_selector___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value:
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
    m_fun: l_Std_Async_Signal_Waiter_selector___lam__8___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__9___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__10___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_Signal_Waiter_selector___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Signal_Waiter_selector___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_Signal_Waiter_selector___lam__3 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Signal_Waiter_selector___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Async_Signal_ctorIdx(mut v_x_1181_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_1181_ {
        0 => {
            let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1182_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1182_;
        }
        1 => {
            let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1183_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1183_;
        }
        2 => {
            let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1184_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1184_;
        }
        3 => {
            let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1185_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1185_;
        }
        4 => {
            let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1186_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1186_;
        }
        5 => {
            let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1187_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1187_;
        }
        6 => {
            let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1188_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1188_;
        }
        7 => {
            let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1189_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1189_;
        }
        8 => {
            let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1190_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1190_;
        }
        9 => {
            let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1191_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_1191_;
        }
        10 => {
            let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1192_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_1192_;
        }
        11 => {
            let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1193_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_1193_;
        }
        12 => {
            let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1194_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_1194_;
        }
        13 => {
            let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1195_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_1195_;
        }
        14 => {
            let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1196_ = crate::leanh::lean_unsigned_to_nat(14);
            return v___x_1196_;
        }
        15 => {
            let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1197_ = crate::leanh::lean_unsigned_to_nat(15);
            return v___x_1197_;
        }
        16 => {
            let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1198_ = crate::leanh::lean_unsigned_to_nat(16);
            return v___x_1198_;
        }
        17 => {
            let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1199_ = crate::leanh::lean_unsigned_to_nat(17);
            return v___x_1199_;
        }
        18 => {
            let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1200_ = crate::leanh::lean_unsigned_to_nat(18);
            return v___x_1200_;
        }
        19 => {
            let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1201_ = crate::leanh::lean_unsigned_to_nat(19);
            return v___x_1201_;
        }
        20 => {
            let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1202_ = crate::leanh::lean_unsigned_to_nat(20);
            return v___x_1202_;
        }
        _ => {
            let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1203_ = crate::leanh::lean_unsigned_to_nat(21);
            return v___x_1203_;
        }
    }
}
pub unsafe fn l_Std_Async_Signal_ctorIdx___boxed(
    mut v_x_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1205_: u8 = 0;
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1205_ = (crate::leanh::lean_unbox(v_x_1204_) as u8);
    v_res_1206_ = l_Std_Async_Signal_ctorIdx(v_x_boxed_1205_);
    return v_res_1206_;
}
pub unsafe fn l_Std_Async_Signal_toCtorIdx(mut v_x_1207_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Std_Async_Signal_ctorIdx(v_x_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Std_Async_Signal_toCtorIdx___boxed(
    mut v_x_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1210_: u8 = 0;
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1210_ = (crate::leanh::lean_unbox(v_x_1209_) as u8);
    v_res_1211_ = l_Std_Async_Signal_toCtorIdx(v_x_4__boxed_1210_);
    return v_res_1211_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim___redArg(
    mut v_k_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1212_);
    return v_k_1212_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim___redArg___boxed(
    mut v_k_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1214_ = l_Std_Async_Signal_ctorElim___redArg(v_k_1213_);
    crate::leanh::lean_dec(v_k_1213_);
    return v_res_1214_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim(
    mut v_motive_1215_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1216_: *mut crate::leanh::LeanObject,
    mut v_t_1217_: u8,
    mut v_h_1218_: *mut crate::leanh::LeanObject,
    mut v_k_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1219_);
    return v_k_1219_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim___boxed(
    mut v_motive_1220_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1221_: *mut crate::leanh::LeanObject,
    mut v_t_1222_: *mut crate::leanh::LeanObject,
    mut v_h_1223_: *mut crate::leanh::LeanObject,
    mut v_k_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1225_: u8 = 0;
    let mut v_res_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1225_ = (crate::leanh::lean_unbox(v_t_1222_) as u8);
    v_res_1226_ = l_Std_Async_Signal_ctorElim(
        v_motive_1220_,
        v_ctorIdx_1221_,
        v_t_boxed_1225_,
        v_h_1223_,
        v_k_1224_,
    );
    crate::leanh::lean_dec(v_k_1224_);
    crate::leanh::lean_dec(v_ctorIdx_1221_);
    return v_res_1226_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim___redArg(
    mut v_sighup_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sighup_1227_);
    return v_sighup_1227_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim___redArg___boxed(
    mut v_sighup_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Std_Async_Signal_sighup_elim___redArg(v_sighup_1228_);
    crate::leanh::lean_dec(v_sighup_1228_);
    return v_res_1229_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim(
    mut v_motive_1230_: *mut crate::leanh::LeanObject,
    mut v_t_1231_: u8,
    mut v_h_1232_: *mut crate::leanh::LeanObject,
    mut v_sighup_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sighup_1233_);
    return v_sighup_1233_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim___boxed(
    mut v_motive_1234_: *mut crate::leanh::LeanObject,
    mut v_t_1235_: *mut crate::leanh::LeanObject,
    mut v_h_1236_: *mut crate::leanh::LeanObject,
    mut v_sighup_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1238_: u8 = 0;
    let mut v_res_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1238_ = (crate::leanh::lean_unbox(v_t_1235_) as u8);
    v_res_1239_ =
        l_Std_Async_Signal_sighup_elim(v_motive_1234_, v_t_boxed_1238_, v_h_1236_, v_sighup_1237_);
    crate::leanh::lean_dec(v_sighup_1237_);
    return v_res_1239_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim___redArg(
    mut v_sigint_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigint_1240_);
    return v_sigint_1240_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim___redArg___boxed(
    mut v_sigint_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_Std_Async_Signal_sigint_elim___redArg(v_sigint_1241_);
    crate::leanh::lean_dec(v_sigint_1241_);
    return v_res_1242_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim(
    mut v_motive_1243_: *mut crate::leanh::LeanObject,
    mut v_t_1244_: u8,
    mut v_h_1245_: *mut crate::leanh::LeanObject,
    mut v_sigint_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigint_1246_);
    return v_sigint_1246_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim___boxed(
    mut v_motive_1247_: *mut crate::leanh::LeanObject,
    mut v_t_1248_: *mut crate::leanh::LeanObject,
    mut v_h_1249_: *mut crate::leanh::LeanObject,
    mut v_sigint_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1251_: u8 = 0;
    let mut v_res_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1251_ = (crate::leanh::lean_unbox(v_t_1248_) as u8);
    v_res_1252_ =
        l_Std_Async_Signal_sigint_elim(v_motive_1247_, v_t_boxed_1251_, v_h_1249_, v_sigint_1250_);
    crate::leanh::lean_dec(v_sigint_1250_);
    return v_res_1252_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim___redArg(
    mut v_sigquit_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigquit_1253_);
    return v_sigquit_1253_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim___redArg___boxed(
    mut v_sigquit_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_Std_Async_Signal_sigquit_elim___redArg(v_sigquit_1254_);
    crate::leanh::lean_dec(v_sigquit_1254_);
    return v_res_1255_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim(
    mut v_motive_1256_: *mut crate::leanh::LeanObject,
    mut v_t_1257_: u8,
    mut v_h_1258_: *mut crate::leanh::LeanObject,
    mut v_sigquit_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigquit_1259_);
    return v_sigquit_1259_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim___boxed(
    mut v_motive_1260_: *mut crate::leanh::LeanObject,
    mut v_t_1261_: *mut crate::leanh::LeanObject,
    mut v_h_1262_: *mut crate::leanh::LeanObject,
    mut v_sigquit_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1264_: u8 = 0;
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1264_ = (crate::leanh::lean_unbox(v_t_1261_) as u8);
    v_res_1265_ = l_Std_Async_Signal_sigquit_elim(
        v_motive_1260_,
        v_t_boxed_1264_,
        v_h_1262_,
        v_sigquit_1263_,
    );
    crate::leanh::lean_dec(v_sigquit_1263_);
    return v_res_1265_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim___redArg(
    mut v_sigtrap_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigtrap_1266_);
    return v_sigtrap_1266_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim___redArg___boxed(
    mut v_sigtrap_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Std_Async_Signal_sigtrap_elim___redArg(v_sigtrap_1267_);
    crate::leanh::lean_dec(v_sigtrap_1267_);
    return v_res_1268_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim(
    mut v_motive_1269_: *mut crate::leanh::LeanObject,
    mut v_t_1270_: u8,
    mut v_h_1271_: *mut crate::leanh::LeanObject,
    mut v_sigtrap_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigtrap_1272_);
    return v_sigtrap_1272_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim___boxed(
    mut v_motive_1273_: *mut crate::leanh::LeanObject,
    mut v_t_1274_: *mut crate::leanh::LeanObject,
    mut v_h_1275_: *mut crate::leanh::LeanObject,
    mut v_sigtrap_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1277_: u8 = 0;
    let mut v_res_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1277_ = (crate::leanh::lean_unbox(v_t_1274_) as u8);
    v_res_1278_ = l_Std_Async_Signal_sigtrap_elim(
        v_motive_1273_,
        v_t_boxed_1277_,
        v_h_1275_,
        v_sigtrap_1276_,
    );
    crate::leanh::lean_dec(v_sigtrap_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim___redArg(
    mut v_sigabrt_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigabrt_1279_);
    return v_sigabrt_1279_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim___redArg___boxed(
    mut v_sigabrt_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Std_Async_Signal_sigabrt_elim___redArg(v_sigabrt_1280_);
    crate::leanh::lean_dec(v_sigabrt_1280_);
    return v_res_1281_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim(
    mut v_motive_1282_: *mut crate::leanh::LeanObject,
    mut v_t_1283_: u8,
    mut v_h_1284_: *mut crate::leanh::LeanObject,
    mut v_sigabrt_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigabrt_1285_);
    return v_sigabrt_1285_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim___boxed(
    mut v_motive_1286_: *mut crate::leanh::LeanObject,
    mut v_t_1287_: *mut crate::leanh::LeanObject,
    mut v_h_1288_: *mut crate::leanh::LeanObject,
    mut v_sigabrt_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1290_: u8 = 0;
    let mut v_res_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1290_ = (crate::leanh::lean_unbox(v_t_1287_) as u8);
    v_res_1291_ = l_Std_Async_Signal_sigabrt_elim(
        v_motive_1286_,
        v_t_boxed_1290_,
        v_h_1288_,
        v_sigabrt_1289_,
    );
    crate::leanh::lean_dec(v_sigabrt_1289_);
    return v_res_1291_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim___redArg(
    mut v_sigusr1_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigusr1_1292_);
    return v_sigusr1_1292_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim___redArg___boxed(
    mut v_sigusr1_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_Async_Signal_sigusr1_elim___redArg(v_sigusr1_1293_);
    crate::leanh::lean_dec(v_sigusr1_1293_);
    return v_res_1294_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim(
    mut v_motive_1295_: *mut crate::leanh::LeanObject,
    mut v_t_1296_: u8,
    mut v_h_1297_: *mut crate::leanh::LeanObject,
    mut v_sigusr1_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigusr1_1298_);
    return v_sigusr1_1298_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim___boxed(
    mut v_motive_1299_: *mut crate::leanh::LeanObject,
    mut v_t_1300_: *mut crate::leanh::LeanObject,
    mut v_h_1301_: *mut crate::leanh::LeanObject,
    mut v_sigusr1_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1303_: u8 = 0;
    let mut v_res_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1303_ = (crate::leanh::lean_unbox(v_t_1300_) as u8);
    v_res_1304_ = l_Std_Async_Signal_sigusr1_elim(
        v_motive_1299_,
        v_t_boxed_1303_,
        v_h_1301_,
        v_sigusr1_1302_,
    );
    crate::leanh::lean_dec(v_sigusr1_1302_);
    return v_res_1304_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim___redArg(
    mut v_sigusr2_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigusr2_1305_);
    return v_sigusr2_1305_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim___redArg___boxed(
    mut v_sigusr2_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Std_Async_Signal_sigusr2_elim___redArg(v_sigusr2_1306_);
    crate::leanh::lean_dec(v_sigusr2_1306_);
    return v_res_1307_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim(
    mut v_motive_1308_: *mut crate::leanh::LeanObject,
    mut v_t_1309_: u8,
    mut v_h_1310_: *mut crate::leanh::LeanObject,
    mut v_sigusr2_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigusr2_1311_);
    return v_sigusr2_1311_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim___boxed(
    mut v_motive_1312_: *mut crate::leanh::LeanObject,
    mut v_t_1313_: *mut crate::leanh::LeanObject,
    mut v_h_1314_: *mut crate::leanh::LeanObject,
    mut v_sigusr2_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1316_: u8 = 0;
    let mut v_res_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1316_ = (crate::leanh::lean_unbox(v_t_1313_) as u8);
    v_res_1317_ = l_Std_Async_Signal_sigusr2_elim(
        v_motive_1312_,
        v_t_boxed_1316_,
        v_h_1314_,
        v_sigusr2_1315_,
    );
    crate::leanh::lean_dec(v_sigusr2_1315_);
    return v_res_1317_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim___redArg(
    mut v_sigalrm_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigalrm_1318_);
    return v_sigalrm_1318_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim___redArg___boxed(
    mut v_sigalrm_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Std_Async_Signal_sigalrm_elim___redArg(v_sigalrm_1319_);
    crate::leanh::lean_dec(v_sigalrm_1319_);
    return v_res_1320_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim(
    mut v_motive_1321_: *mut crate::leanh::LeanObject,
    mut v_t_1322_: u8,
    mut v_h_1323_: *mut crate::leanh::LeanObject,
    mut v_sigalrm_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigalrm_1324_);
    return v_sigalrm_1324_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim___boxed(
    mut v_motive_1325_: *mut crate::leanh::LeanObject,
    mut v_t_1326_: *mut crate::leanh::LeanObject,
    mut v_h_1327_: *mut crate::leanh::LeanObject,
    mut v_sigalrm_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1329_ = (crate::leanh::lean_unbox(v_t_1326_) as u8);
    v_res_1330_ = l_Std_Async_Signal_sigalrm_elim(
        v_motive_1325_,
        v_t_boxed_1329_,
        v_h_1327_,
        v_sigalrm_1328_,
    );
    crate::leanh::lean_dec(v_sigalrm_1328_);
    return v_res_1330_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim___redArg(
    mut v_sigterm_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigterm_1331_);
    return v_sigterm_1331_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim___redArg___boxed(
    mut v_sigterm_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_Std_Async_Signal_sigterm_elim___redArg(v_sigterm_1332_);
    crate::leanh::lean_dec(v_sigterm_1332_);
    return v_res_1333_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim(
    mut v_motive_1334_: *mut crate::leanh::LeanObject,
    mut v_t_1335_: u8,
    mut v_h_1336_: *mut crate::leanh::LeanObject,
    mut v_sigterm_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigterm_1337_);
    return v_sigterm_1337_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim___boxed(
    mut v_motive_1338_: *mut crate::leanh::LeanObject,
    mut v_t_1339_: *mut crate::leanh::LeanObject,
    mut v_h_1340_: *mut crate::leanh::LeanObject,
    mut v_sigterm_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1342_: u8 = 0;
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1342_ = (crate::leanh::lean_unbox(v_t_1339_) as u8);
    v_res_1343_ = l_Std_Async_Signal_sigterm_elim(
        v_motive_1338_,
        v_t_boxed_1342_,
        v_h_1340_,
        v_sigterm_1341_,
    );
    crate::leanh::lean_dec(v_sigterm_1341_);
    return v_res_1343_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim___redArg(
    mut v_sigchld_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigchld_1344_);
    return v_sigchld_1344_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim___redArg___boxed(
    mut v_sigchld_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Std_Async_Signal_sigchld_elim___redArg(v_sigchld_1345_);
    crate::leanh::lean_dec(v_sigchld_1345_);
    return v_res_1346_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim(
    mut v_motive_1347_: *mut crate::leanh::LeanObject,
    mut v_t_1348_: u8,
    mut v_h_1349_: *mut crate::leanh::LeanObject,
    mut v_sigchld_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigchld_1350_);
    return v_sigchld_1350_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim___boxed(
    mut v_motive_1351_: *mut crate::leanh::LeanObject,
    mut v_t_1352_: *mut crate::leanh::LeanObject,
    mut v_h_1353_: *mut crate::leanh::LeanObject,
    mut v_sigchld_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1355_: u8 = 0;
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1355_ = (crate::leanh::lean_unbox(v_t_1352_) as u8);
    v_res_1356_ = l_Std_Async_Signal_sigchld_elim(
        v_motive_1351_,
        v_t_boxed_1355_,
        v_h_1353_,
        v_sigchld_1354_,
    );
    crate::leanh::lean_dec(v_sigchld_1354_);
    return v_res_1356_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim___redArg(
    mut v_sigcont_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigcont_1357_);
    return v_sigcont_1357_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim___redArg___boxed(
    mut v_sigcont_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Std_Async_Signal_sigcont_elim___redArg(v_sigcont_1358_);
    crate::leanh::lean_dec(v_sigcont_1358_);
    return v_res_1359_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim(
    mut v_motive_1360_: *mut crate::leanh::LeanObject,
    mut v_t_1361_: u8,
    mut v_h_1362_: *mut crate::leanh::LeanObject,
    mut v_sigcont_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigcont_1363_);
    return v_sigcont_1363_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim___boxed(
    mut v_motive_1364_: *mut crate::leanh::LeanObject,
    mut v_t_1365_: *mut crate::leanh::LeanObject,
    mut v_h_1366_: *mut crate::leanh::LeanObject,
    mut v_sigcont_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1368_ = (crate::leanh::lean_unbox(v_t_1365_) as u8);
    v_res_1369_ = l_Std_Async_Signal_sigcont_elim(
        v_motive_1364_,
        v_t_boxed_1368_,
        v_h_1366_,
        v_sigcont_1367_,
    );
    crate::leanh::lean_dec(v_sigcont_1367_);
    return v_res_1369_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim___redArg(
    mut v_sigtstp_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigtstp_1370_);
    return v_sigtstp_1370_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim___redArg___boxed(
    mut v_sigtstp_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Std_Async_Signal_sigtstp_elim___redArg(v_sigtstp_1371_);
    crate::leanh::lean_dec(v_sigtstp_1371_);
    return v_res_1372_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim(
    mut v_motive_1373_: *mut crate::leanh::LeanObject,
    mut v_t_1374_: u8,
    mut v_h_1375_: *mut crate::leanh::LeanObject,
    mut v_sigtstp_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigtstp_1376_);
    return v_sigtstp_1376_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim___boxed(
    mut v_motive_1377_: *mut crate::leanh::LeanObject,
    mut v_t_1378_: *mut crate::leanh::LeanObject,
    mut v_h_1379_: *mut crate::leanh::LeanObject,
    mut v_sigtstp_1380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1381_: u8 = 0;
    let mut v_res_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1381_ = (crate::leanh::lean_unbox(v_t_1378_) as u8);
    v_res_1382_ = l_Std_Async_Signal_sigtstp_elim(
        v_motive_1377_,
        v_t_boxed_1381_,
        v_h_1379_,
        v_sigtstp_1380_,
    );
    crate::leanh::lean_dec(v_sigtstp_1380_);
    return v_res_1382_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim___redArg(
    mut v_sigttin_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigttin_1383_);
    return v_sigttin_1383_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim___redArg___boxed(
    mut v_sigttin_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Std_Async_Signal_sigttin_elim___redArg(v_sigttin_1384_);
    crate::leanh::lean_dec(v_sigttin_1384_);
    return v_res_1385_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim(
    mut v_motive_1386_: *mut crate::leanh::LeanObject,
    mut v_t_1387_: u8,
    mut v_h_1388_: *mut crate::leanh::LeanObject,
    mut v_sigttin_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigttin_1389_);
    return v_sigttin_1389_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim___boxed(
    mut v_motive_1390_: *mut crate::leanh::LeanObject,
    mut v_t_1391_: *mut crate::leanh::LeanObject,
    mut v_h_1392_: *mut crate::leanh::LeanObject,
    mut v_sigttin_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1394_: u8 = 0;
    let mut v_res_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1394_ = (crate::leanh::lean_unbox(v_t_1391_) as u8);
    v_res_1395_ = l_Std_Async_Signal_sigttin_elim(
        v_motive_1390_,
        v_t_boxed_1394_,
        v_h_1392_,
        v_sigttin_1393_,
    );
    crate::leanh::lean_dec(v_sigttin_1393_);
    return v_res_1395_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim___redArg(
    mut v_sigttou_1396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigttou_1396_);
    return v_sigttou_1396_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim___redArg___boxed(
    mut v_sigttou_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Std_Async_Signal_sigttou_elim___redArg(v_sigttou_1397_);
    crate::leanh::lean_dec(v_sigttou_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim(
    mut v_motive_1399_: *mut crate::leanh::LeanObject,
    mut v_t_1400_: u8,
    mut v_h_1401_: *mut crate::leanh::LeanObject,
    mut v_sigttou_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigttou_1402_);
    return v_sigttou_1402_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim___boxed(
    mut v_motive_1403_: *mut crate::leanh::LeanObject,
    mut v_t_1404_: *mut crate::leanh::LeanObject,
    mut v_h_1405_: *mut crate::leanh::LeanObject,
    mut v_sigttou_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1407_: u8 = 0;
    let mut v_res_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1407_ = (crate::leanh::lean_unbox(v_t_1404_) as u8);
    v_res_1408_ = l_Std_Async_Signal_sigttou_elim(
        v_motive_1403_,
        v_t_boxed_1407_,
        v_h_1405_,
        v_sigttou_1406_,
    );
    crate::leanh::lean_dec(v_sigttou_1406_);
    return v_res_1408_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim___redArg(
    mut v_sigurg_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigurg_1409_);
    return v_sigurg_1409_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim___redArg___boxed(
    mut v_sigurg_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Std_Async_Signal_sigurg_elim___redArg(v_sigurg_1410_);
    crate::leanh::lean_dec(v_sigurg_1410_);
    return v_res_1411_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim(
    mut v_motive_1412_: *mut crate::leanh::LeanObject,
    mut v_t_1413_: u8,
    mut v_h_1414_: *mut crate::leanh::LeanObject,
    mut v_sigurg_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigurg_1415_);
    return v_sigurg_1415_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim___boxed(
    mut v_motive_1416_: *mut crate::leanh::LeanObject,
    mut v_t_1417_: *mut crate::leanh::LeanObject,
    mut v_h_1418_: *mut crate::leanh::LeanObject,
    mut v_sigurg_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1420_: u8 = 0;
    let mut v_res_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1420_ = (crate::leanh::lean_unbox(v_t_1417_) as u8);
    v_res_1421_ =
        l_Std_Async_Signal_sigurg_elim(v_motive_1416_, v_t_boxed_1420_, v_h_1418_, v_sigurg_1419_);
    crate::leanh::lean_dec(v_sigurg_1419_);
    return v_res_1421_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim___redArg(
    mut v_sigxcpu_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigxcpu_1422_);
    return v_sigxcpu_1422_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(
    mut v_sigxcpu_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Std_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_1423_);
    crate::leanh::lean_dec(v_sigxcpu_1423_);
    return v_res_1424_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim(
    mut v_motive_1425_: *mut crate::leanh::LeanObject,
    mut v_t_1426_: u8,
    mut v_h_1427_: *mut crate::leanh::LeanObject,
    mut v_sigxcpu_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigxcpu_1428_);
    return v_sigxcpu_1428_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim___boxed(
    mut v_motive_1429_: *mut crate::leanh::LeanObject,
    mut v_t_1430_: *mut crate::leanh::LeanObject,
    mut v_h_1431_: *mut crate::leanh::LeanObject,
    mut v_sigxcpu_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1433_: u8 = 0;
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1433_ = (crate::leanh::lean_unbox(v_t_1430_) as u8);
    v_res_1434_ = l_Std_Async_Signal_sigxcpu_elim(
        v_motive_1429_,
        v_t_boxed_1433_,
        v_h_1431_,
        v_sigxcpu_1432_,
    );
    crate::leanh::lean_dec(v_sigxcpu_1432_);
    return v_res_1434_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim___redArg(
    mut v_sigxfsz_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigxfsz_1435_);
    return v_sigxfsz_1435_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(
    mut v_sigxfsz_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Std_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_1436_);
    crate::leanh::lean_dec(v_sigxfsz_1436_);
    return v_res_1437_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim(
    mut v_motive_1438_: *mut crate::leanh::LeanObject,
    mut v_t_1439_: u8,
    mut v_h_1440_: *mut crate::leanh::LeanObject,
    mut v_sigxfsz_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigxfsz_1441_);
    return v_sigxfsz_1441_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim___boxed(
    mut v_motive_1442_: *mut crate::leanh::LeanObject,
    mut v_t_1443_: *mut crate::leanh::LeanObject,
    mut v_h_1444_: *mut crate::leanh::LeanObject,
    mut v_sigxfsz_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1446_: u8 = 0;
    let mut v_res_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1446_ = (crate::leanh::lean_unbox(v_t_1443_) as u8);
    v_res_1447_ = l_Std_Async_Signal_sigxfsz_elim(
        v_motive_1442_,
        v_t_boxed_1446_,
        v_h_1444_,
        v_sigxfsz_1445_,
    );
    crate::leanh::lean_dec(v_sigxfsz_1445_);
    return v_res_1447_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim___redArg(
    mut v_sigvtalrm_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigvtalrm_1448_);
    return v_sigvtalrm_1448_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(
    mut v_sigvtalrm_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Std_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_1449_);
    crate::leanh::lean_dec(v_sigvtalrm_1449_);
    return v_res_1450_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim(
    mut v_motive_1451_: *mut crate::leanh::LeanObject,
    mut v_t_1452_: u8,
    mut v_h_1453_: *mut crate::leanh::LeanObject,
    mut v_sigvtalrm_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigvtalrm_1454_);
    return v_sigvtalrm_1454_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim___boxed(
    mut v_motive_1455_: *mut crate::leanh::LeanObject,
    mut v_t_1456_: *mut crate::leanh::LeanObject,
    mut v_h_1457_: *mut crate::leanh::LeanObject,
    mut v_sigvtalrm_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1459_: u8 = 0;
    let mut v_res_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1459_ = (crate::leanh::lean_unbox(v_t_1456_) as u8);
    v_res_1460_ = l_Std_Async_Signal_sigvtalrm_elim(
        v_motive_1455_,
        v_t_boxed_1459_,
        v_h_1457_,
        v_sigvtalrm_1458_,
    );
    crate::leanh::lean_dec(v_sigvtalrm_1458_);
    return v_res_1460_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim___redArg(
    mut v_sigprof_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigprof_1461_);
    return v_sigprof_1461_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim___redArg___boxed(
    mut v_sigprof_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Std_Async_Signal_sigprof_elim___redArg(v_sigprof_1462_);
    crate::leanh::lean_dec(v_sigprof_1462_);
    return v_res_1463_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim(
    mut v_motive_1464_: *mut crate::leanh::LeanObject,
    mut v_t_1465_: u8,
    mut v_h_1466_: *mut crate::leanh::LeanObject,
    mut v_sigprof_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigprof_1467_);
    return v_sigprof_1467_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim___boxed(
    mut v_motive_1468_: *mut crate::leanh::LeanObject,
    mut v_t_1469_: *mut crate::leanh::LeanObject,
    mut v_h_1470_: *mut crate::leanh::LeanObject,
    mut v_sigprof_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1472_: u8 = 0;
    let mut v_res_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1472_ = (crate::leanh::lean_unbox(v_t_1469_) as u8);
    v_res_1473_ = l_Std_Async_Signal_sigprof_elim(
        v_motive_1468_,
        v_t_boxed_1472_,
        v_h_1470_,
        v_sigprof_1471_,
    );
    crate::leanh::lean_dec(v_sigprof_1471_);
    return v_res_1473_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim___redArg(
    mut v_sigwinch_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigwinch_1474_);
    return v_sigwinch_1474_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim___redArg___boxed(
    mut v_sigwinch_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1476_ = l_Std_Async_Signal_sigwinch_elim___redArg(v_sigwinch_1475_);
    crate::leanh::lean_dec(v_sigwinch_1475_);
    return v_res_1476_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim(
    mut v_motive_1477_: *mut crate::leanh::LeanObject,
    mut v_t_1478_: u8,
    mut v_h_1479_: *mut crate::leanh::LeanObject,
    mut v_sigwinch_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigwinch_1480_);
    return v_sigwinch_1480_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim___boxed(
    mut v_motive_1481_: *mut crate::leanh::LeanObject,
    mut v_t_1482_: *mut crate::leanh::LeanObject,
    mut v_h_1483_: *mut crate::leanh::LeanObject,
    mut v_sigwinch_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1485_: u8 = 0;
    let mut v_res_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1485_ = (crate::leanh::lean_unbox(v_t_1482_) as u8);
    v_res_1486_ = l_Std_Async_Signal_sigwinch_elim(
        v_motive_1481_,
        v_t_boxed_1485_,
        v_h_1483_,
        v_sigwinch_1484_,
    );
    crate::leanh::lean_dec(v_sigwinch_1484_);
    return v_res_1486_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim___redArg(
    mut v_sigio_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigio_1487_);
    return v_sigio_1487_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim___redArg___boxed(
    mut v_sigio_1488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1489_ = l_Std_Async_Signal_sigio_elim___redArg(v_sigio_1488_);
    crate::leanh::lean_dec(v_sigio_1488_);
    return v_res_1489_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim(
    mut v_motive_1490_: *mut crate::leanh::LeanObject,
    mut v_t_1491_: u8,
    mut v_h_1492_: *mut crate::leanh::LeanObject,
    mut v_sigio_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigio_1493_);
    return v_sigio_1493_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim___boxed(
    mut v_motive_1494_: *mut crate::leanh::LeanObject,
    mut v_t_1495_: *mut crate::leanh::LeanObject,
    mut v_h_1496_: *mut crate::leanh::LeanObject,
    mut v_sigio_1497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1498_: u8 = 0;
    let mut v_res_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1498_ = (crate::leanh::lean_unbox(v_t_1495_) as u8);
    v_res_1499_ =
        l_Std_Async_Signal_sigio_elim(v_motive_1494_, v_t_boxed_1498_, v_h_1496_, v_sigio_1497_);
    crate::leanh::lean_dec(v_sigio_1497_);
    return v_res_1499_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim___redArg(
    mut v_sigsys_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigsys_1500_);
    return v_sigsys_1500_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim___redArg___boxed(
    mut v_sigsys_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Std_Async_Signal_sigsys_elim___redArg(v_sigsys_1501_);
    crate::leanh::lean_dec(v_sigsys_1501_);
    return v_res_1502_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim(
    mut v_motive_1503_: *mut crate::leanh::LeanObject,
    mut v_t_1504_: u8,
    mut v_h_1505_: *mut crate::leanh::LeanObject,
    mut v_sigsys_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_sigsys_1506_);
    return v_sigsys_1506_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim___boxed(
    mut v_motive_1507_: *mut crate::leanh::LeanObject,
    mut v_t_1508_: *mut crate::leanh::LeanObject,
    mut v_h_1509_: *mut crate::leanh::LeanObject,
    mut v_sigsys_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1511_: u8 = 0;
    let mut v_res_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1511_ = (crate::leanh::lean_unbox(v_t_1508_) as u8);
    v_res_1512_ =
        l_Std_Async_Signal_sigsys_elim(v_motive_1507_, v_t_boxed_1511_, v_h_1509_, v_sigsys_1510_);
    crate::leanh::lean_dec(v_sigsys_1510_);
    return v_res_1512_;
}
pub unsafe fn _init_l_Std_Async_instReprSignal_repr___closed__44() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1579_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1580_ = lean_nat_to_int(v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn _init_l_Std_Async_instReprSignal_repr___closed__45() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1582_ = lean_nat_to_int(v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn l_Std_Async_instReprSignal_repr(
    mut v_x_1583_: u8,
    mut v_prec_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: u8 = 0;
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u8 = 0;
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1583_ {
                0 => {
                    v___x_1739_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1740_ = lean_nat_dec_le(v___x_1739_, v_prec_1584_);
                    if v___x_1740_ == 0 {
                        v___x_1741_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1586_ = v___x_1741_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1742_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1586_ = v___x_1742_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1743_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1744_ = lean_nat_dec_le(v___x_1743_, v_prec_1584_);
                    if v___x_1744_ == 0 {
                        v___x_1745_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1593_ = v___x_1745_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1746_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1593_ = v___x_1746_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_1747_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1748_ = lean_nat_dec_le(v___x_1747_, v_prec_1584_);
                    if v___x_1748_ == 0 {
                        v___x_1749_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1600_ = v___x_1749_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1750_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1600_ = v___x_1750_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_1751_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1752_ = lean_nat_dec_le(v___x_1751_, v_prec_1584_);
                    if v___x_1752_ == 0 {
                        v___x_1753_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1607_ = v___x_1753_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1754_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1607_ = v___x_1754_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_1755_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1756_ = lean_nat_dec_le(v___x_1755_, v_prec_1584_);
                    if v___x_1756_ == 0 {
                        v___x_1757_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1614_ = v___x_1757_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1758_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1614_ = v___x_1758_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v___x_1759_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1760_ = lean_nat_dec_le(v___x_1759_, v_prec_1584_);
                    if v___x_1760_ == 0 {
                        v___x_1761_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1621_ = v___x_1761_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1762_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1621_ = v___x_1762_;
                        state = 6;
                        continue;
                    }
                }
                6 => {
                    v___x_1763_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1764_ = lean_nat_dec_le(v___x_1763_, v_prec_1584_);
                    if v___x_1764_ == 0 {
                        v___x_1765_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1628_ = v___x_1765_;
                        state = 7;
                        continue;
                    } else {
                        v___x_1766_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1628_ = v___x_1766_;
                        state = 7;
                        continue;
                    }
                }
                7 => {
                    v___x_1767_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1768_ = lean_nat_dec_le(v___x_1767_, v_prec_1584_);
                    if v___x_1768_ == 0 {
                        v___x_1769_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1635_ = v___x_1769_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1770_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1635_ = v___x_1770_;
                        state = 8;
                        continue;
                    }
                }
                8 => {
                    v___x_1771_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1772_ = lean_nat_dec_le(v___x_1771_, v_prec_1584_);
                    if v___x_1772_ == 0 {
                        v___x_1773_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1642_ = v___x_1773_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1774_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1642_ = v___x_1774_;
                        state = 9;
                        continue;
                    }
                }
                9 => {
                    v___x_1775_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1776_ = lean_nat_dec_le(v___x_1775_, v_prec_1584_);
                    if v___x_1776_ == 0 {
                        v___x_1777_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1649_ = v___x_1777_;
                        state = 10;
                        continue;
                    } else {
                        v___x_1778_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1649_ = v___x_1778_;
                        state = 10;
                        continue;
                    }
                }
                10 => {
                    v___x_1779_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1780_ = lean_nat_dec_le(v___x_1779_, v_prec_1584_);
                    if v___x_1780_ == 0 {
                        v___x_1781_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1656_ = v___x_1781_;
                        state = 11;
                        continue;
                    } else {
                        v___x_1782_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1656_ = v___x_1782_;
                        state = 11;
                        continue;
                    }
                }
                11 => {
                    v___x_1783_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1784_ = lean_nat_dec_le(v___x_1783_, v_prec_1584_);
                    if v___x_1784_ == 0 {
                        v___x_1785_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1663_ = v___x_1785_;
                        state = 12;
                        continue;
                    } else {
                        v___x_1786_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1663_ = v___x_1786_;
                        state = 12;
                        continue;
                    }
                }
                12 => {
                    v___x_1787_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1788_ = lean_nat_dec_le(v___x_1787_, v_prec_1584_);
                    if v___x_1788_ == 0 {
                        v___x_1789_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1670_ = v___x_1789_;
                        state = 13;
                        continue;
                    } else {
                        v___x_1790_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1670_ = v___x_1790_;
                        state = 13;
                        continue;
                    }
                }
                13 => {
                    v___x_1791_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1792_ = lean_nat_dec_le(v___x_1791_, v_prec_1584_);
                    if v___x_1792_ == 0 {
                        v___x_1793_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1677_ = v___x_1793_;
                        state = 14;
                        continue;
                    } else {
                        v___x_1794_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1677_ = v___x_1794_;
                        state = 14;
                        continue;
                    }
                }
                14 => {
                    v___x_1795_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1796_ = lean_nat_dec_le(v___x_1795_, v_prec_1584_);
                    if v___x_1796_ == 0 {
                        v___x_1797_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1684_ = v___x_1797_;
                        state = 15;
                        continue;
                    } else {
                        v___x_1798_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1684_ = v___x_1798_;
                        state = 15;
                        continue;
                    }
                }
                15 => {
                    v___x_1799_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1800_ = lean_nat_dec_le(v___x_1799_, v_prec_1584_);
                    if v___x_1800_ == 0 {
                        v___x_1801_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1691_ = v___x_1801_;
                        state = 16;
                        continue;
                    } else {
                        v___x_1802_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1691_ = v___x_1802_;
                        state = 16;
                        continue;
                    }
                }
                16 => {
                    v___x_1803_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1804_ = lean_nat_dec_le(v___x_1803_, v_prec_1584_);
                    if v___x_1804_ == 0 {
                        v___x_1805_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1698_ = v___x_1805_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1806_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1698_ = v___x_1806_;
                        state = 17;
                        continue;
                    }
                }
                17 => {
                    v___x_1807_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1808_ = lean_nat_dec_le(v___x_1807_, v_prec_1584_);
                    if v___x_1808_ == 0 {
                        v___x_1809_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1705_ = v___x_1809_;
                        state = 18;
                        continue;
                    } else {
                        v___x_1810_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1705_ = v___x_1810_;
                        state = 18;
                        continue;
                    }
                }
                18 => {
                    v___x_1811_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1812_ = lean_nat_dec_le(v___x_1811_, v_prec_1584_);
                    if v___x_1812_ == 0 {
                        v___x_1813_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1712_ = v___x_1813_;
                        state = 19;
                        continue;
                    } else {
                        v___x_1814_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1712_ = v___x_1814_;
                        state = 19;
                        continue;
                    }
                }
                19 => {
                    v___x_1815_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1816_ = lean_nat_dec_le(v___x_1815_, v_prec_1584_);
                    if v___x_1816_ == 0 {
                        v___x_1817_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1719_ = v___x_1817_;
                        state = 20;
                        continue;
                    } else {
                        v___x_1818_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1719_ = v___x_1818_;
                        state = 20;
                        continue;
                    }
                }
                20 => {
                    v___x_1819_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1820_ = lean_nat_dec_le(v___x_1819_, v_prec_1584_);
                    if v___x_1820_ == 0 {
                        v___x_1821_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1726_ = v___x_1821_;
                        state = 21;
                        continue;
                    } else {
                        v___x_1822_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1726_ = v___x_1822_;
                        state = 21;
                        continue;
                    }
                }
                _ => {
                    v___x_1823_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1824_ = lean_nat_dec_le(v___x_1823_, v_prec_1584_);
                    if v___x_1824_ == 0 {
                        v___x_1825_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__44),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__44_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__44,
                        );
                        v___y_1733_ = v___x_1825_;
                        state = 22;
                        continue;
                    } else {
                        v___x_1826_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Async_instReprSignal_repr___closed__45),
                            core::ptr::addr_of_mut!(
                                l_Std_Async_instReprSignal_repr___closed__45_once
                            ),
                            _init_l_Std_Async_instReprSignal_repr___closed__45,
                        );
                        v___y_1733_ = v___x_1826_;
                        state = 22;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1587_ = l_Std_Async_instReprSignal_repr___closed__1;
                crate::leanh::lean_inc(v___y_1586_);
                v___x_1588_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1588_, 0, v___y_1586_);
                crate::leanh::lean_ctor_set(v___x_1588_, 1, v___x_1587_);
                v___x_1589_ = 0;
                v___x_1590_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1590_, 0, v___x_1588_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1589_,
                );
                v___x_1591_ = l_Repr_addAppParen(v___x_1590_, v_prec_1584_);
                return v___x_1591_;
            }
            2 => {
                v___x_1594_ = l_Std_Async_instReprSignal_repr___closed__3;
                crate::leanh::lean_inc(v___y_1593_);
                v___x_1595_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1595_, 0, v___y_1593_);
                crate::leanh::lean_ctor_set(v___x_1595_, 1, v___x_1594_);
                v___x_1596_ = 0;
                v___x_1597_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1595_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1597_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1596_,
                );
                v___x_1598_ = l_Repr_addAppParen(v___x_1597_, v_prec_1584_);
                return v___x_1598_;
            }
            3 => {
                v___x_1601_ = l_Std_Async_instReprSignal_repr___closed__5;
                crate::leanh::lean_inc(v___y_1600_);
                v___x_1602_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1602_, 0, v___y_1600_);
                crate::leanh::lean_ctor_set(v___x_1602_, 1, v___x_1601_);
                v___x_1603_ = 0;
                v___x_1604_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1602_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1604_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1603_,
                );
                v___x_1605_ = l_Repr_addAppParen(v___x_1604_, v_prec_1584_);
                return v___x_1605_;
            }
            4 => {
                v___x_1608_ = l_Std_Async_instReprSignal_repr___closed__7;
                crate::leanh::lean_inc(v___y_1607_);
                v___x_1609_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1609_, 0, v___y_1607_);
                crate::leanh::lean_ctor_set(v___x_1609_, 1, v___x_1608_);
                v___x_1610_ = 0;
                v___x_1611_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1611_, 0, v___x_1609_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1611_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1610_,
                );
                v___x_1612_ = l_Repr_addAppParen(v___x_1611_, v_prec_1584_);
                return v___x_1612_;
            }
            5 => {
                v___x_1615_ = l_Std_Async_instReprSignal_repr___closed__9;
                crate::leanh::lean_inc(v___y_1614_);
                v___x_1616_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1616_, 0, v___y_1614_);
                crate::leanh::lean_ctor_set(v___x_1616_, 1, v___x_1615_);
                v___x_1617_ = 0;
                v___x_1618_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1617_,
                );
                v___x_1619_ = l_Repr_addAppParen(v___x_1618_, v_prec_1584_);
                return v___x_1619_;
            }
            6 => {
                v___x_1622_ = l_Std_Async_instReprSignal_repr___closed__11;
                crate::leanh::lean_inc(v___y_1621_);
                v___x_1623_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1623_, 0, v___y_1621_);
                crate::leanh::lean_ctor_set(v___x_1623_, 1, v___x_1622_);
                v___x_1624_ = 0;
                v___x_1625_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1625_, 0, v___x_1623_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1625_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1624_,
                );
                v___x_1626_ = l_Repr_addAppParen(v___x_1625_, v_prec_1584_);
                return v___x_1626_;
            }
            7 => {
                v___x_1629_ = l_Std_Async_instReprSignal_repr___closed__13;
                crate::leanh::lean_inc(v___y_1628_);
                v___x_1630_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1630_, 0, v___y_1628_);
                crate::leanh::lean_ctor_set(v___x_1630_, 1, v___x_1629_);
                v___x_1631_ = 0;
                v___x_1632_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1632_, 0, v___x_1630_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1632_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1631_,
                );
                v___x_1633_ = l_Repr_addAppParen(v___x_1632_, v_prec_1584_);
                return v___x_1633_;
            }
            8 => {
                v___x_1636_ = l_Std_Async_instReprSignal_repr___closed__15;
                crate::leanh::lean_inc(v___y_1635_);
                v___x_1637_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1637_, 0, v___y_1635_);
                crate::leanh::lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                v___x_1638_ = 0;
                v___x_1639_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1639_, 0, v___x_1637_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1638_,
                );
                v___x_1640_ = l_Repr_addAppParen(v___x_1639_, v_prec_1584_);
                return v___x_1640_;
            }
            9 => {
                v___x_1643_ = l_Std_Async_instReprSignal_repr___closed__17;
                crate::leanh::lean_inc(v___y_1642_);
                v___x_1644_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1644_, 0, v___y_1642_);
                crate::leanh::lean_ctor_set(v___x_1644_, 1, v___x_1643_);
                v___x_1645_ = 0;
                v___x_1646_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1644_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1646_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1645_,
                );
                v___x_1647_ = l_Repr_addAppParen(v___x_1646_, v_prec_1584_);
                return v___x_1647_;
            }
            10 => {
                v___x_1650_ = l_Std_Async_instReprSignal_repr___closed__19;
                crate::leanh::lean_inc(v___y_1649_);
                v___x_1651_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1651_, 0, v___y_1649_);
                crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1650_);
                v___x_1652_ = 0;
                v___x_1653_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1651_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1653_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1652_,
                );
                v___x_1654_ = l_Repr_addAppParen(v___x_1653_, v_prec_1584_);
                return v___x_1654_;
            }
            11 => {
                v___x_1657_ = l_Std_Async_instReprSignal_repr___closed__21;
                crate::leanh::lean_inc(v___y_1656_);
                v___x_1658_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1658_, 0, v___y_1656_);
                crate::leanh::lean_ctor_set(v___x_1658_, 1, v___x_1657_);
                v___x_1659_ = 0;
                v___x_1660_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1660_, 0, v___x_1658_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1660_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1659_,
                );
                v___x_1661_ = l_Repr_addAppParen(v___x_1660_, v_prec_1584_);
                return v___x_1661_;
            }
            12 => {
                v___x_1664_ = l_Std_Async_instReprSignal_repr___closed__23;
                crate::leanh::lean_inc(v___y_1663_);
                v___x_1665_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___y_1663_);
                crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v___x_1666_ = 0;
                v___x_1667_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1665_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1667_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1666_,
                );
                v___x_1668_ = l_Repr_addAppParen(v___x_1667_, v_prec_1584_);
                return v___x_1668_;
            }
            13 => {
                v___x_1671_ = l_Std_Async_instReprSignal_repr___closed__25;
                crate::leanh::lean_inc(v___y_1670_);
                v___x_1672_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1672_, 0, v___y_1670_);
                crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                v___x_1673_ = 0;
                v___x_1674_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1674_, 0, v___x_1672_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1674_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1673_,
                );
                v___x_1675_ = l_Repr_addAppParen(v___x_1674_, v_prec_1584_);
                return v___x_1675_;
            }
            14 => {
                v___x_1678_ = l_Std_Async_instReprSignal_repr___closed__27;
                crate::leanh::lean_inc(v___y_1677_);
                v___x_1679_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1679_, 0, v___y_1677_);
                crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
                v___x_1680_ = 0;
                v___x_1681_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1679_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1681_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1680_,
                );
                v___x_1682_ = l_Repr_addAppParen(v___x_1681_, v_prec_1584_);
                return v___x_1682_;
            }
            15 => {
                v___x_1685_ = l_Std_Async_instReprSignal_repr___closed__29;
                crate::leanh::lean_inc(v___y_1684_);
                v___x_1686_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1686_, 0, v___y_1684_);
                crate::leanh::lean_ctor_set(v___x_1686_, 1, v___x_1685_);
                v___x_1687_ = 0;
                v___x_1688_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1686_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1688_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1687_,
                );
                v___x_1689_ = l_Repr_addAppParen(v___x_1688_, v_prec_1584_);
                return v___x_1689_;
            }
            16 => {
                v___x_1692_ = l_Std_Async_instReprSignal_repr___closed__31;
                crate::leanh::lean_inc(v___y_1691_);
                v___x_1693_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1693_, 0, v___y_1691_);
                crate::leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                v___x_1694_ = 0;
                v___x_1695_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1695_, 0, v___x_1693_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1694_,
                );
                v___x_1696_ = l_Repr_addAppParen(v___x_1695_, v_prec_1584_);
                return v___x_1696_;
            }
            17 => {
                v___x_1699_ = l_Std_Async_instReprSignal_repr___closed__33;
                crate::leanh::lean_inc(v___y_1698_);
                v___x_1700_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1700_, 0, v___y_1698_);
                crate::leanh::lean_ctor_set(v___x_1700_, 1, v___x_1699_);
                v___x_1701_ = 0;
                v___x_1702_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1702_, 0, v___x_1700_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1702_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1701_,
                );
                v___x_1703_ = l_Repr_addAppParen(v___x_1702_, v_prec_1584_);
                return v___x_1703_;
            }
            18 => {
                v___x_1706_ = l_Std_Async_instReprSignal_repr___closed__35;
                crate::leanh::lean_inc(v___y_1705_);
                v___x_1707_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1707_, 0, v___y_1705_);
                crate::leanh::lean_ctor_set(v___x_1707_, 1, v___x_1706_);
                v___x_1708_ = 0;
                v___x_1709_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1709_, 0, v___x_1707_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1709_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1708_,
                );
                v___x_1710_ = l_Repr_addAppParen(v___x_1709_, v_prec_1584_);
                return v___x_1710_;
            }
            19 => {
                v___x_1713_ = l_Std_Async_instReprSignal_repr___closed__37;
                crate::leanh::lean_inc(v___y_1712_);
                v___x_1714_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1714_, 0, v___y_1712_);
                crate::leanh::lean_ctor_set(v___x_1714_, 1, v___x_1713_);
                v___x_1715_ = 0;
                v___x_1716_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1716_, 0, v___x_1714_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1716_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1715_,
                );
                v___x_1717_ = l_Repr_addAppParen(v___x_1716_, v_prec_1584_);
                return v___x_1717_;
            }
            20 => {
                v___x_1720_ = l_Std_Async_instReprSignal_repr___closed__39;
                crate::leanh::lean_inc(v___y_1719_);
                v___x_1721_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1721_, 0, v___y_1719_);
                crate::leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                v___x_1722_ = 0;
                v___x_1723_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1723_, 0, v___x_1721_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1722_,
                );
                v___x_1724_ = l_Repr_addAppParen(v___x_1723_, v_prec_1584_);
                return v___x_1724_;
            }
            21 => {
                v___x_1727_ = l_Std_Async_instReprSignal_repr___closed__41;
                crate::leanh::lean_inc(v___y_1726_);
                v___x_1728_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1728_, 0, v___y_1726_);
                crate::leanh::lean_ctor_set(v___x_1728_, 1, v___x_1727_);
                v___x_1729_ = 0;
                v___x_1730_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1730_, 0, v___x_1728_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1729_,
                );
                v___x_1731_ = l_Repr_addAppParen(v___x_1730_, v_prec_1584_);
                return v___x_1731_;
            }
            22 => {
                v___x_1734_ = l_Std_Async_instReprSignal_repr___closed__43;
                crate::leanh::lean_inc(v___y_1733_);
                v___x_1735_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1735_, 0, v___y_1733_);
                crate::leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
                v___x_1736_ = 0;
                v___x_1737_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1737_, 0, v___x_1735_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1737_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1736_,
                );
                v___x_1738_ = l_Repr_addAppParen(v___x_1737_, v_prec_1584_);
                return v___x_1738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_instReprSignal_repr___boxed(
    mut v_x_1827_: *mut crate::leanh::LeanObject,
    mut v_prec_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1241__boxed_1829_: u8 = 0;
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1241__boxed_1829_ = (crate::leanh::lean_unbox(v_x_1827_) as u8);
    v_res_1830_ = l_Std_Async_instReprSignal_repr(v_x_1241__boxed_1829_, v_prec_1828_);
    crate::leanh::lean_dec(v_prec_1828_);
    return v_res_1830_;
}
pub unsafe fn l_Std_Async_Signal_ofNat(mut v_n_1833_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    v___x_1834_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1835_ = lean_nat_dec_le(v_n_1833_, v___x_1834_);
    if v___x_1835_ == 0 {
        let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: u8 = 0;
        v___x_1836_ = crate::leanh::lean_unsigned_to_nat(15);
        v___x_1837_ = lean_nat_dec_le(v_n_1833_, v___x_1836_);
        if v___x_1837_ == 0 {
            let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1839_: u8 = 0;
            v___x_1838_ = crate::leanh::lean_unsigned_to_nat(18);
            v___x_1839_ = lean_nat_dec_le(v_n_1833_, v___x_1838_);
            if v___x_1839_ == 0 {
                let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1841_: u8 = 0;
                v___x_1840_ = crate::leanh::lean_unsigned_to_nat(19);
                v___x_1841_ = lean_nat_dec_le(v_n_1833_, v___x_1840_);
                if v___x_1841_ == 0 {
                    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1843_: u8 = 0;
                    v___x_1842_ = crate::leanh::lean_unsigned_to_nat(20);
                    v___x_1843_ = lean_nat_dec_le(v_n_1833_, v___x_1842_);
                    if v___x_1843_ == 0 {
                        let mut v___x_1844_: u8 = 0;
                        v___x_1844_ = 21;
                        return v___x_1844_;
                    } else {
                        let mut v___x_1845_: u8 = 0;
                        v___x_1845_ = 20;
                        return v___x_1845_;
                    }
                } else {
                    let mut v___x_1846_: u8 = 0;
                    v___x_1846_ = 19;
                    return v___x_1846_;
                }
            } else {
                let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1848_: u8 = 0;
                v___x_1847_ = crate::leanh::lean_unsigned_to_nat(16);
                v___x_1848_ = lean_nat_dec_le(v_n_1833_, v___x_1847_);
                if v___x_1848_ == 0 {
                    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1850_: u8 = 0;
                    v___x_1849_ = crate::leanh::lean_unsigned_to_nat(17);
                    v___x_1850_ = lean_nat_dec_le(v_n_1833_, v___x_1849_);
                    if v___x_1850_ == 0 {
                        let mut v___x_1851_: u8 = 0;
                        v___x_1851_ = 18;
                        return v___x_1851_;
                    } else {
                        let mut v___x_1852_: u8 = 0;
                        v___x_1852_ = 17;
                        return v___x_1852_;
                    }
                } else {
                    let mut v___x_1853_: u8 = 0;
                    v___x_1853_ = 16;
                    return v___x_1853_;
                }
            }
        } else {
            let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1855_: u8 = 0;
            v___x_1854_ = crate::leanh::lean_unsigned_to_nat(12);
            v___x_1855_ = lean_nat_dec_le(v_n_1833_, v___x_1854_);
            if v___x_1855_ == 0 {
                let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1857_: u8 = 0;
                v___x_1856_ = crate::leanh::lean_unsigned_to_nat(13);
                v___x_1857_ = lean_nat_dec_le(v_n_1833_, v___x_1856_);
                if v___x_1857_ == 0 {
                    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1859_: u8 = 0;
                    v___x_1858_ = crate::leanh::lean_unsigned_to_nat(14);
                    v___x_1859_ = lean_nat_dec_le(v_n_1833_, v___x_1858_);
                    if v___x_1859_ == 0 {
                        let mut v___x_1860_: u8 = 0;
                        v___x_1860_ = 15;
                        return v___x_1860_;
                    } else {
                        let mut v___x_1861_: u8 = 0;
                        v___x_1861_ = 14;
                        return v___x_1861_;
                    }
                } else {
                    let mut v___x_1862_: u8 = 0;
                    v___x_1862_ = 13;
                    return v___x_1862_;
                }
            } else {
                let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1864_: u8 = 0;
                v___x_1863_ = crate::leanh::lean_unsigned_to_nat(11);
                v___x_1864_ = lean_nat_dec_le(v_n_1833_, v___x_1863_);
                if v___x_1864_ == 0 {
                    let mut v___x_1865_: u8 = 0;
                    v___x_1865_ = 12;
                    return v___x_1865_;
                } else {
                    let mut v___x_1866_: u8 = 0;
                    v___x_1866_ = 11;
                    return v___x_1866_;
                }
            }
        }
    } else {
        let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: u8 = 0;
        v___x_1867_ = crate::leanh::lean_unsigned_to_nat(4);
        v___x_1868_ = lean_nat_dec_le(v_n_1833_, v___x_1867_);
        if v___x_1868_ == 0 {
            let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1870_: u8 = 0;
            v___x_1869_ = crate::leanh::lean_unsigned_to_nat(7);
            v___x_1870_ = lean_nat_dec_le(v_n_1833_, v___x_1869_);
            if v___x_1870_ == 0 {
                let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1872_: u8 = 0;
                v___x_1871_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_1872_ = lean_nat_dec_le(v_n_1833_, v___x_1871_);
                if v___x_1872_ == 0 {
                    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1874_: u8 = 0;
                    v___x_1873_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_1874_ = lean_nat_dec_le(v_n_1833_, v___x_1873_);
                    if v___x_1874_ == 0 {
                        let mut v___x_1875_: u8 = 0;
                        v___x_1875_ = 10;
                        return v___x_1875_;
                    } else {
                        let mut v___x_1876_: u8 = 0;
                        v___x_1876_ = 9;
                        return v___x_1876_;
                    }
                } else {
                    let mut v___x_1877_: u8 = 0;
                    v___x_1877_ = 8;
                    return v___x_1877_;
                }
            } else {
                let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1879_: u8 = 0;
                v___x_1878_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_1879_ = lean_nat_dec_le(v_n_1833_, v___x_1878_);
                if v___x_1879_ == 0 {
                    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1881_: u8 = 0;
                    v___x_1880_ = crate::leanh::lean_unsigned_to_nat(6);
                    v___x_1881_ = lean_nat_dec_le(v_n_1833_, v___x_1880_);
                    if v___x_1881_ == 0 {
                        let mut v___x_1882_: u8 = 0;
                        v___x_1882_ = 7;
                        return v___x_1882_;
                    } else {
                        let mut v___x_1883_: u8 = 0;
                        v___x_1883_ = 6;
                        return v___x_1883_;
                    }
                } else {
                    let mut v___x_1884_: u8 = 0;
                    v___x_1884_ = 5;
                    return v___x_1884_;
                }
            }
        } else {
            let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1886_: u8 = 0;
            v___x_1885_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1886_ = lean_nat_dec_le(v_n_1833_, v___x_1885_);
            if v___x_1886_ == 0 {
                let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1888_: u8 = 0;
                v___x_1887_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1888_ = lean_nat_dec_le(v_n_1833_, v___x_1887_);
                if v___x_1888_ == 0 {
                    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1890_: u8 = 0;
                    v___x_1889_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1890_ = lean_nat_dec_le(v_n_1833_, v___x_1889_);
                    if v___x_1890_ == 0 {
                        let mut v___x_1891_: u8 = 0;
                        v___x_1891_ = 4;
                        return v___x_1891_;
                    } else {
                        let mut v___x_1892_: u8 = 0;
                        v___x_1892_ = 3;
                        return v___x_1892_;
                    }
                } else {
                    let mut v___x_1893_: u8 = 0;
                    v___x_1893_ = 2;
                    return v___x_1893_;
                }
            } else {
                let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1895_: u8 = 0;
                v___x_1894_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1895_ = lean_nat_dec_le(v_n_1833_, v___x_1894_);
                if v___x_1895_ == 0 {
                    let mut v___x_1896_: u8 = 0;
                    v___x_1896_ = 1;
                    return v___x_1896_;
                } else {
                    let mut v___x_1897_: u8 = 0;
                    v___x_1897_ = 0;
                    return v___x_1897_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Async_Signal_ofNat___boxed(
    mut v_n_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1899_: u8 = 0;
    let mut v_r_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l_Std_Async_Signal_ofNat(v_n_1898_);
    crate::leanh::lean_dec(v_n_1898_);
    v_r_1900_ = crate::leanh::lean_box((v_res_1899_) as usize);
    return v_r_1900_;
}
pub unsafe fn l_Std_Async_instDecidableEqSignal(mut v_x_1901_: u8, mut v_y_1902_: u8) -> u8 {
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u8 = 0;
    v___x_1903_ = l_Std_Async_Signal_ctorIdx(v_x_1901_);
    v___x_1904_ = l_Std_Async_Signal_ctorIdx(v_y_1902_);
    v___x_1905_ = lean_nat_dec_eq(v___x_1903_, v___x_1904_);
    crate::leanh::lean_dec(v___x_1904_);
    crate::leanh::lean_dec(v___x_1903_);
    return v___x_1905_;
}
pub unsafe fn l_Std_Async_instDecidableEqSignal___boxed(
    mut v_x_1906_: *mut crate::leanh::LeanObject,
    mut v_y_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_1908_: u8 = 0;
    let mut v_y_14__boxed_1909_: u8 = 0;
    let mut v_res_1910_: u8 = 0;
    let mut v_r_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_1908_ = (crate::leanh::lean_unbox(v_x_1906_) as u8);
    v_y_14__boxed_1909_ = (crate::leanh::lean_unbox(v_y_1907_) as u8);
    v_res_1910_ = l_Std_Async_instDecidableEqSignal(v_x_13__boxed_1908_, v_y_14__boxed_1909_);
    v_r_1911_ = crate::leanh::lean_box((v_res_1910_) as usize);
    return v_r_1911_;
}
pub unsafe fn l_Std_Async_instBEqSignal_beq(mut v_x_1912_: u8, mut v_y_1913_: u8) -> u8 {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u8 = 0;
    v___x_1914_ = l_Std_Async_Signal_ctorIdx(v_x_1912_);
    v___x_1915_ = l_Std_Async_Signal_ctorIdx(v_y_1913_);
    v___x_1916_ = lean_nat_dec_eq(v___x_1914_, v___x_1915_);
    crate::leanh::lean_dec(v___x_1915_);
    crate::leanh::lean_dec(v___x_1914_);
    return v___x_1916_;
}
pub unsafe fn l_Std_Async_instBEqSignal_beq___boxed(
    mut v_x_1917_: *mut crate::leanh::LeanObject,
    mut v_y_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1919_: u8 = 0;
    let mut v_y_18__boxed_1920_: u8 = 0;
    let mut v_res_1921_: u8 = 0;
    let mut v_r_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1919_ = (crate::leanh::lean_unbox(v_x_1917_) as u8);
    v_y_18__boxed_1920_ = (crate::leanh::lean_unbox(v_y_1918_) as u8);
    v_res_1921_ = l_Std_Async_instBEqSignal_beq(v_x_17__boxed_1919_, v_y_18__boxed_1920_);
    v_r_1922_ = crate::leanh::lean_box((v_res_1921_) as usize);
    return v_r_1922_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0() -> u32 {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u32 = 0;
    v___x_1925_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1926_ = lean_int32_of_nat(v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1() -> u32 {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: u32 = 0;
    v___x_1927_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1928_ = lean_int32_of_nat(v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2() -> u32 {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u32 = 0;
    v___x_1929_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1930_ = lean_int32_of_nat(v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3() -> u32 {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u32 = 0;
    v___x_1931_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_1932_ = lean_int32_of_nat(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4() -> u32 {
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u32 = 0;
    v___x_1933_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_1934_ = lean_int32_of_nat(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5() -> u32 {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: u32 = 0;
    v___x_1935_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1936_ = lean_int32_of_nat(v___x_1935_);
    return v___x_1936_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6() -> u32 {
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u32 = 0;
    v___x_1937_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_1938_ = lean_int32_of_nat(v___x_1937_);
    return v___x_1938_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7() -> u32 {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u32 = 0;
    v___x_1939_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1940_ = lean_int32_of_nat(v___x_1939_);
    return v___x_1940_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8() -> u32 {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u32 = 0;
    v___x_1941_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_1942_ = lean_int32_of_nat(v___x_1941_);
    return v___x_1942_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9() -> u32 {
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u32 = 0;
    v___x_1943_ = crate::leanh::lean_unsigned_to_nat(17);
    v___x_1944_ = lean_int32_of_nat(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10() -> u32 {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u32 = 0;
    v___x_1945_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_1946_ = lean_int32_of_nat(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11() -> u32 {
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u32 = 0;
    v___x_1947_ = crate::leanh::lean_unsigned_to_nat(20);
    v___x_1948_ = lean_int32_of_nat(v___x_1947_);
    return v___x_1948_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12() -> u32 {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u32 = 0;
    v___x_1949_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1950_ = lean_int32_of_nat(v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13() -> u32 {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u32 = 0;
    v___x_1951_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_1952_ = lean_int32_of_nat(v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14() -> u32 {
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u32 = 0;
    v___x_1953_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_1954_ = lean_int32_of_nat(v___x_1953_);
    return v___x_1954_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15() -> u32 {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u32 = 0;
    v___x_1955_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_1956_ = lean_int32_of_nat(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16() -> u32 {
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u32 = 0;
    v___x_1957_ = crate::leanh::lean_unsigned_to_nat(25);
    v___x_1958_ = lean_int32_of_nat(v___x_1957_);
    return v___x_1958_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17() -> u32 {
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u32 = 0;
    v___x_1959_ = crate::leanh::lean_unsigned_to_nat(26);
    v___x_1960_ = lean_int32_of_nat(v___x_1959_);
    return v___x_1960_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18() -> u32 {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u32 = 0;
    v___x_1961_ = crate::leanh::lean_unsigned_to_nat(27);
    v___x_1962_ = lean_int32_of_nat(v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19() -> u32 {
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u32 = 0;
    v___x_1963_ = crate::leanh::lean_unsigned_to_nat(28);
    v___x_1964_ = lean_int32_of_nat(v___x_1963_);
    return v___x_1964_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20() -> u32 {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u32 = 0;
    v___x_1965_ = crate::leanh::lean_unsigned_to_nat(29);
    v___x_1966_ = lean_int32_of_nat(v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21() -> u32 {
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u32 = 0;
    v___x_1967_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_1968_ = lean_int32_of_nat(v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(mut v_x_1969_: u8) -> u32 {
    match v_x_1969_ {
        0 => {
            let mut v___x_1970_: u32 = 0;
            v___x_1970_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0,
            );
            return v___x_1970_;
        }
        1 => {
            let mut v___x_1971_: u32 = 0;
            v___x_1971_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1,
            );
            return v___x_1971_;
        }
        2 => {
            let mut v___x_1972_: u32 = 0;
            v___x_1972_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2,
            );
            return v___x_1972_;
        }
        3 => {
            let mut v___x_1973_: u32 = 0;
            v___x_1973_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3,
            );
            return v___x_1973_;
        }
        4 => {
            let mut v___x_1974_: u32 = 0;
            v___x_1974_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4,
            );
            return v___x_1974_;
        }
        5 => {
            let mut v___x_1975_: u32 = 0;
            v___x_1975_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5,
            );
            return v___x_1975_;
        }
        6 => {
            let mut v___x_1976_: u32 = 0;
            v___x_1976_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6,
            );
            return v___x_1976_;
        }
        7 => {
            let mut v___x_1977_: u32 = 0;
            v___x_1977_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7,
            );
            return v___x_1977_;
        }
        8 => {
            let mut v___x_1978_: u32 = 0;
            v___x_1978_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8,
            );
            return v___x_1978_;
        }
        9 => {
            let mut v___x_1979_: u32 = 0;
            v___x_1979_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9,
            );
            return v___x_1979_;
        }
        10 => {
            let mut v___x_1980_: u32 = 0;
            v___x_1980_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10,
            );
            return v___x_1980_;
        }
        11 => {
            let mut v___x_1981_: u32 = 0;
            v___x_1981_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11,
            );
            return v___x_1981_;
        }
        12 => {
            let mut v___x_1982_: u32 = 0;
            v___x_1982_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12,
            );
            return v___x_1982_;
        }
        13 => {
            let mut v___x_1983_: u32 = 0;
            v___x_1983_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13,
            );
            return v___x_1983_;
        }
        14 => {
            let mut v___x_1984_: u32 = 0;
            v___x_1984_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14,
            );
            return v___x_1984_;
        }
        15 => {
            let mut v___x_1985_: u32 = 0;
            v___x_1985_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15,
            );
            return v___x_1985_;
        }
        16 => {
            let mut v___x_1986_: u32 = 0;
            v___x_1986_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16,
            );
            return v___x_1986_;
        }
        17 => {
            let mut v___x_1987_: u32 = 0;
            v___x_1987_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17,
            );
            return v___x_1987_;
        }
        18 => {
            let mut v___x_1988_: u32 = 0;
            v___x_1988_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18,
            );
            return v___x_1988_;
        }
        19 => {
            let mut v___x_1989_: u32 = 0;
            v___x_1989_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19,
            );
            return v___x_1989_;
        }
        20 => {
            let mut v___x_1990_: u32 = 0;
            v___x_1990_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20,
            );
            return v___x_1990_;
        }
        _ => {
            let mut v___x_1991_: u32 = 0;
            v___x_1991_ = crate::leanh::lean_uint32_once(
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21
                ),
                core::ptr::addr_of_mut!(
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once
                ),
                _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21,
            );
            return v___x_1991_;
        }
    }
}
pub unsafe fn l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___boxed(
    mut v_x_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_356__boxed_1993_: u8 = 0;
    let mut v_res_1994_: u32 = 0;
    let mut v_r_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_356__boxed_1993_ = (crate::leanh::lean_unbox(v_x_1992_) as u8);
    v_res_1994_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_356__boxed_1993_);
    v_r_1995_ = crate::leanh::lean_box_uint32(v_res_1994_);
    return v_r_1995_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_mk(
    mut v_signum_1996_: u8,
    mut v_repeating_1997_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1999_: u32 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v_a_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1999_ =
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_signum_1996_);
                v___x_2000_ = lean_uv_signal_mk(v___x_1999_, v_repeating_1997_);
                if crate::leanh::lean_obj_tag(v___x_2000_) == 0 {
                    v_a_2001_ = crate::leanh::lean_ctor_get(v___x_2000_, 0);
                    v_isSharedCheck_2008_ = (!crate::leanh::lean_is_exclusive(v___x_2000_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_2003_ = v___x_2000_;
                        v_isShared_2004_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2001_);
                        crate::leanh::lean_dec(v___x_2000_);
                        v___x_2003_ = crate::leanh::lean_box(0);
                        v_isShared_2004_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2009_ = crate::leanh::lean_ctor_get(v___x_2000_, 0);
                    v_isSharedCheck_2016_ = (!crate::leanh::lean_is_exclusive(v___x_2000_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2011_ = v___x_2000_;
                        v_isShared_2012_ = v_isSharedCheck_2016_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2009_);
                        crate::leanh::lean_dec(v___x_2000_);
                        v___x_2011_ = crate::leanh::lean_box(0);
                        v_isShared_2012_ = v_isSharedCheck_2016_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2004_ == 0 {
                    v___x_2006_ = v___x_2003_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
                    v___x_2006_ = v_reuseFailAlloc_2007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2006_;
            }
            3 => {
                if v_isShared_2012_ == 0 {
                    v___x_2014_ = v___x_2011_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
                    v___x_2014_ = v_reuseFailAlloc_2015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_mk___boxed(
    mut v_signum_2017_: *mut crate::leanh::LeanObject,
    mut v_repeating_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_signum_boxed_2020_: u8 = 0;
    let mut v_repeating_boxed_2021_: u8 = 0;
    let mut v_res_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_signum_boxed_2020_ = (crate::leanh::lean_unbox(v_signum_2017_) as u8);
    v_repeating_boxed_2021_ = (crate::leanh::lean_unbox(v_repeating_2018_) as u8);
    v_res_2022_ = l_Std_Async_Signal_Waiter_mk(v_signum_boxed_2020_, v_repeating_boxed_2021_);
    return v_res_2022_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_wait___lam__0(
    mut v___x_2023_: *mut crate::leanh::LeanObject,
    mut v_x_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2024_) == 0 {
                    v___x_2025_ = lean_mk_io_user_error(v___x_2023_);
                    v___x_2026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2026_, 0, v___x_2025_);
                    return v___x_2026_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_2023_);
                    v_val_2027_ = crate::leanh::lean_ctor_get(v_x_2024_, 0);
                    v_isSharedCheck_2034_ = (!crate::leanh::lean_is_exclusive(v_x_2024_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2029_ = v_x_2024_;
                        v_isShared_2030_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2027_);
                        crate::leanh::lean_dec(v_x_2024_);
                        v___x_2029_ = crate::leanh::lean_box(0);
                        v_isShared_2030_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2030_ == 0 {
                    v___x_2032_ = v___x_2029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_val_2027_);
                    v___x_2032_ = v_reuseFailAlloc_2033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_wait(
    mut v_s_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v___f_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: u8 = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2053_: u8 = 0;
    let mut v_a_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2040_ = lean_uv_signal_next(v_s_2038_);
                if crate::leanh::lean_obj_tag(v___x_2040_) == 0 {
                    v_a_2041_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2053_ = (!crate::leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2053_ == 0 {
                        v___x_2043_ = v___x_2040_;
                        v_isShared_2044_ = v_isSharedCheck_2053_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2041_);
                        crate::leanh::lean_dec(v___x_2040_);
                        v___x_2043_ = crate::leanh::lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2053_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2054_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2061_ = (!crate::leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2061_ == 0 {
                        v___x_2056_ = v___x_2040_;
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2054_);
                        crate::leanh::lean_dec(v___x_2040_);
                        v___x_2056_ = crate::leanh::lean_box(0);
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_2045_ = l_Std_Async_Signal_Waiter_wait___closed__1;
                v___x_2046_ = lean_io_promise_result_opt(v_a_2041_);
                crate::leanh::lean_dec(v_a_2041_);
                v___x_2047_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2048_ = 1;
                v___x_2049_ = lean_task_map(v___f_2045_, v___x_2046_, v___x_2047_, v___x_2048_);
                if v_isShared_2044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2049_);
                    v___x_2051_ = v___x_2043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
                    v___x_2051_ = v_reuseFailAlloc_2052_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2051_;
            }
            3 => {
                if v_isShared_2057_ == 0 {
                    v___x_2059_ = v___x_2056_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
                    v___x_2059_ = v_reuseFailAlloc_2060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_wait___boxed(
    mut v_s_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Std_Async_Signal_Waiter_wait(v_s_2062_);
    crate::leanh::lean_dec(v_s_2062_);
    return v_res_2064_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_stop(
    mut v_s_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = lean_uv_signal_stop(v_s_2065_);
    return v___x_2067_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_stop___boxed(
    mut v_s_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Std_Async_Signal_Waiter_stop(v_s_2068_);
    crate::leanh::lean_dec(v_s_2068_);
    return v_res_2070_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(
    mut v_w_2073_: *mut crate::leanh::LeanObject,
    mut v_lose_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_finished_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_2076_ = crate::leanh::lean_ctor_get(v_w_2073_, 0);
                v_promise_2077_ = crate::leanh::lean_ctor_get(v_w_2073_, 1);
                v___x_2078_ = lean_st_ref_take(v_finished_2076_);
                v___x_2088_ = (crate::leanh::lean_unbox(v___x_2078_) as u8);
                crate::leanh::lean_dec(v___x_2078_);
                if v___x_2088_ == 0 {
                    v___x_2089_ = 1;
                    v___y_2080_ = v___x_2089_;
                    state = 1;
                    continue;
                } else {
                    v___x_2090_ = 0;
                    v___y_2080_ = v___x_2090_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2081_ = 1;
                v___x_2082_ = crate::leanh::lean_box((v___x_2081_) as usize);
                v___x_2083_ = lean_st_ref_set(v_finished_2076_, v___x_2082_);
                if v___y_2080_ == 0 {
                    v___x_2084_ =
                        crate::leanh::lean_apply_1(v_lose_2074_, crate::leanh::lean_box(0));
                    return v___x_2084_;
                } else {
                    crate::leanh::lean_dec_ref(v_lose_2074_);
                    v___x_2085_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0;
                    v___x_2086_ = lean_io_promise_resolve(v___x_2085_, v_promise_2077_);
                    v___x_2087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2087_, 0, v___x_2086_);
                    return v___x_2087_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(
    mut v_w_2091_: *mut crate::leanh::LeanObject,
    mut v_lose_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2094_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(
        v_w_2091_,
        v_lose_2092_,
    );
    crate::leanh::lean_dec_ref(v_w_2091_);
    return v_res_2094_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__0(
    mut v_s_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2100_ = lean_uv_signal_cancel(v_s_2095_);
                if crate::leanh::lean_obj_tag(v___x_2100_) == 0 {
                    v_a_2101_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                    v_isSharedCheck_2108_ = (!crate::leanh::lean_is_exclusive(v___x_2100_)) as u8;
                    if v_isSharedCheck_2108_ == 0 {
                        v___x_2103_ = v___x_2100_;
                        v_isShared_2104_ = v_isSharedCheck_2108_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2101_);
                        crate::leanh::lean_dec(v___x_2100_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2108_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2100_, 0);
                    v_isSharedCheck_2116_ = (!crate::leanh::lean_is_exclusive(v___x_2100_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2111_ = v___x_2100_;
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2109_);
                        crate::leanh::lean_dec(v___x_2100_);
                        v___x_2111_ = crate::leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2099_, 0, v_val_2098_);
                return v___x_2099_;
            }
            2 => {
                if v_isShared_2104_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2103_, 1);
                    v___x_2106_ = v___x_2103_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
                    v___x_2106_ = v_reuseFailAlloc_2107_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2098_ = v___x_2106_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2112_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2111_, 0);
                    v___x_2114_ = v___x_2111_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
                    v___x_2114_ = v_reuseFailAlloc_2115_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2098_ = v___x_2114_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__0___boxed(
    mut v_s_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2119_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_s_2117_);
    crate::leanh::lean_dec(v_s_2117_);
    return v_res_2119_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__1(
    mut v_x_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2124_) == 0 {
                    v_a_2126_ = crate::leanh::lean_ctor_get(v_x_2124_, 0);
                    v_isSharedCheck_2134_ = (!crate::leanh::lean_is_exclusive(v_x_2124_)) as u8;
                    if v_isSharedCheck_2134_ == 0 {
                        v___x_2128_ = v_x_2124_;
                        v_isShared_2129_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2126_);
                        crate::leanh::lean_dec(v_x_2124_);
                        v___x_2128_ = crate::leanh::lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_2124_, 1);
                    v___x_2135_ = l_Std_Async_Signal_Waiter_selector___lam__1___closed__1;
                    return v___x_2135_;
                }
            }
            1 => {
                if v_isShared_2129_ == 0 {
                    v___x_2131_ = v___x_2128_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2126_);
                    v___x_2131_ = v_reuseFailAlloc_2133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                return v___x_2132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__1___boxed(
    mut v_x_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Std_Async_Signal_Waiter_selector___lam__1(v_x_2136_);
    return v_res_2138_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__2(
    mut v___f_2145_: *mut crate::leanh::LeanObject,
    mut v_s_2146_: *mut crate::leanh::LeanObject,
    mut v_x_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_a_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_val_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2147_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2145_);
                    v_a_2149_ = crate::leanh::lean_ctor_get(v_x_2147_, 0);
                    v_isSharedCheck_2157_ = (!crate::leanh::lean_is_exclusive(v_x_2147_)) as u8;
                    if v_isSharedCheck_2157_ == 0 {
                        v___x_2151_ = v_x_2147_;
                        v_isShared_2152_ = v_isSharedCheck_2157_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2149_);
                        crate::leanh::lean_dec(v_x_2147_);
                        v___x_2151_ = crate::leanh::lean_box(0);
                        v_isShared_2152_ = v_isSharedCheck_2157_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2158_ = crate::leanh::lean_ctor_get(v_x_2147_, 0);
                    v_isSharedCheck_2179_ = (!crate::leanh::lean_is_exclusive(v_x_2147_)) as u8;
                    if v_isSharedCheck_2179_ == 0 {
                        v___x_2160_ = v_x_2147_;
                        v_isShared_2161_ = v_isSharedCheck_2179_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2158_);
                        crate::leanh::lean_dec(v_x_2147_);
                        v___x_2160_ = crate::leanh::lean_box(0);
                        v_isShared_2161_ = v_isSharedCheck_2179_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2152_ == 0 {
                    v___x_2154_ = v___x_2151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2149_);
                    v___x_2154_ = v_reuseFailAlloc_2156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                return v___x_2155_;
            }
            3 => {
                v___x_2168_ = (crate::leanh::lean_unbox(v_a_2158_) as u8);
                if v___x_2168_ == 0 {
                    v___x_2169_ = lean_uv_signal_cancel(v_s_2146_);
                    if crate::leanh::lean_obj_tag(v___x_2169_) == 0 {
                        v_a_2170_ = crate::leanh::lean_ctor_get(v___x_2169_, 0);
                        crate::leanh::lean_inc(v_a_2170_);
                        crate::leanh::lean_dec_ref_known(v___x_2169_, 1);
                        if v_isShared_2161_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2160_, 0, v_a_2170_);
                            v___x_2172_ = v___x_2160_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2173_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2170_);
                            v___x_2172_ = v_reuseFailAlloc_2173_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2174_ = crate::leanh::lean_ctor_get(v___x_2169_, 0);
                        crate::leanh::lean_inc(v_a_2174_);
                        crate::leanh::lean_dec_ref_known(v___x_2169_, 1);
                        if v_isShared_2161_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2160_, 0);
                            crate::leanh::lean_ctor_set(v___x_2160_, 0, v_a_2174_);
                            v___x_2176_ = v___x_2160_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2177_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2174_);
                            v___x_2176_ = v_reuseFailAlloc_2177_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2160_);
                    crate::leanh::lean_dec(v_a_2158_);
                    crate::leanh::lean_dec_ref(v___f_2145_);
                    v___x_2178_ = l_Std_Async_Signal_Waiter_selector___lam__2___closed__2;
                    return v___x_2178_;
                }
            }
            4 => {
                v___x_2164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2164_, 0, v_val_2163_);
                v___x_2165_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2166_ = (crate::leanh::lean_unbox(v_a_2158_) as u8);
                crate::leanh::lean_dec(v_a_2158_);
                v___x_2167_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2165_,
                    v___x_2166_,
                    v___x_2164_,
                    v___f_2145_,
                );
                return v___x_2167_;
            }
            5 => {
                v_val_2163_ = v___x_2172_;
                state = 4;
                continue;
            }
            6 => {
                v_val_2163_ = v___x_2176_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__2___boxed(
    mut v___f_2180_: *mut crate::leanh::LeanObject,
    mut v_s_2181_: *mut crate::leanh::LeanObject,
    mut v_x_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Std_Async_Signal_Waiter_selector___lam__2(v___f_2180_, v_s_2181_, v_x_2182_);
    crate::leanh::lean_dec(v_s_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__3(
    mut v_x_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2185_) == 0 {
        let mut v_a_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2186_ = crate::leanh::lean_ctor_get(v_x_2185_, 0);
        crate::leanh::lean_inc(v_a_2186_);
        crate::leanh::lean_dec_ref_known(v_x_2185_, 1);
        v___x_2187_ = lean_task_pure(v_a_2186_);
        return v___x_2187_;
    } else {
        let mut v_a_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2188_ = crate::leanh::lean_ctor_get(v_x_2185_, 0);
        crate::leanh::lean_inc_ref(v_a_2188_);
        crate::leanh::lean_dec_ref_known(v_x_2185_, 1);
        return v_a_2188_;
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__5(
    mut v_s_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2198_: u8 = 0;
    let mut v___f_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_a_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2194_ = lean_uv_signal_next(v_s_2189_);
                if crate::leanh::lean_obj_tag(v___x_2194_) == 0 {
                    v_a_2195_ = crate::leanh::lean_ctor_get(v___x_2194_, 0);
                    v_isSharedCheck_2207_ = (!crate::leanh::lean_is_exclusive(v___x_2194_)) as u8;
                    if v_isSharedCheck_2207_ == 0 {
                        v___x_2197_ = v___x_2194_;
                        v_isShared_2198_ = v_isSharedCheck_2207_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2195_);
                        crate::leanh::lean_dec(v___x_2194_);
                        v___x_2197_ = crate::leanh::lean_box(0);
                        v_isShared_2198_ = v_isSharedCheck_2207_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2208_ = crate::leanh::lean_ctor_get(v___x_2194_, 0);
                    v_isSharedCheck_2215_ = (!crate::leanh::lean_is_exclusive(v___x_2194_)) as u8;
                    if v_isSharedCheck_2215_ == 0 {
                        v___x_2210_ = v___x_2194_;
                        v_isShared_2211_ = v_isSharedCheck_2215_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2208_);
                        crate::leanh::lean_dec(v___x_2194_);
                        v___x_2210_ = crate::leanh::lean_box(0);
                        v_isShared_2211_ = v_isSharedCheck_2215_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2193_, 0, v_val_2192_);
                return v___x_2193_;
            }
            2 => {
                v___f_2199_ = l_Std_Async_Signal_Waiter_wait___closed__1;
                v___x_2200_ = lean_io_promise_result_opt(v_a_2195_);
                crate::leanh::lean_dec(v_a_2195_);
                v___x_2201_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2202_ = 1;
                v___x_2203_ = lean_task_map(v___f_2199_, v___x_2200_, v___x_2201_, v___x_2202_);
                if v_isShared_2198_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2197_, 1);
                    crate::leanh::lean_ctor_set(v___x_2197_, 0, v___x_2203_);
                    v___x_2205_ = v___x_2197_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
                    v___x_2205_ = v_reuseFailAlloc_2206_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2192_ = v___x_2205_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2211_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2210_, 0);
                    v___x_2213_ = v___x_2210_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
                    v___x_2213_ = v_reuseFailAlloc_2214_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2192_ = v___x_2213_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__5___boxed(
    mut v_s_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_2216_);
    crate::leanh::lean_dec(v_s_2216_);
    return v_res_2218_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__4(
    mut v___f_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2221_ = crate::leanh::lean_apply_1(v___f_2219_, crate::leanh::lean_box(0));
    return v___x_2221_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__4___boxed(
    mut v___f_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Std_Async_Signal_Waiter_selector___lam__4(v___f_2222_);
    return v_res_2224_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__6(
    mut v___x_2225_: *mut crate::leanh::LeanObject,
    mut v___f_2226_: *mut crate::leanh::LeanObject,
    mut v_x_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: u8 = 0;
    let mut v_val_2244_: u8 = 0;
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: u8 = 0;
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2227_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2226_);
                    crate::leanh::lean_dec(v___x_2225_);
                    v_a_2229_ = crate::leanh::lean_ctor_get(v_x_2227_, 0);
                    v_isSharedCheck_2237_ = (!crate::leanh::lean_is_exclusive(v_x_2227_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2231_ = v_x_2227_;
                        v_isShared_2232_ = v_isSharedCheck_2237_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2229_);
                        crate::leanh::lean_dec(v_x_2227_);
                        v___x_2231_ = crate::leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2237_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2238_ = crate::leanh::lean_ctor_get(v_x_2227_, 0);
                    v_isSharedCheck_2254_ = (!crate::leanh::lean_is_exclusive(v_x_2227_)) as u8;
                    if v_isSharedCheck_2254_ == 0 {
                        v___x_2240_ = v_x_2227_;
                        v_isShared_2241_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2238_);
                        crate::leanh::lean_dec(v_x_2227_);
                        v___x_2240_ = crate::leanh::lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2232_ == 0 {
                    v___x_2234_ = v___x_2231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2234_);
                return v___x_2235_;
            }
            3 => {
                v___x_2242_ = lean_io_get_task_state(v_a_2238_);
                crate::leanh::lean_dec(v_a_2238_);
                if v___x_2242_ == 2 {
                    v___x_2252_ = 1;
                    v_val_2244_ = v___x_2252_;
                    state = 4;
                    continue;
                } else {
                    v___x_2253_ = 0;
                    v_val_2244_ = v___x_2253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2245_ = crate::leanh::lean_box((v_val_2244_) as usize);
                if v_isShared_2241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2245_);
                    v___x_2247_ = v___x_2240_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2245_);
                    v___x_2247_ = v_reuseFailAlloc_2251_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2248_, 0, v___x_2247_);
                v___x_2249_ = 0;
                v___x_2250_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2225_,
                    v___x_2249_,
                    v___x_2248_,
                    v___f_2226_,
                );
                return v___x_2250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__6___boxed(
    mut v___x_2255_: *mut crate::leanh::LeanObject,
    mut v___f_2256_: *mut crate::leanh::LeanObject,
    mut v_x_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2259_ = l_Std_Async_Signal_Waiter_selector___lam__6(v___x_2255_, v___f_2256_, v_x_2257_);
    return v_res_2259_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__7(
    mut v___f_2260_: *mut crate::leanh::LeanObject,
    mut v___x_2261_: *mut crate::leanh::LeanObject,
    mut v___f_2262_: *mut crate::leanh::LeanObject,
    mut v___f_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v___x_2261_, 2);
    v___x_2265_ = lean_io_as_task(v___f_2260_, v___x_2261_);
    v___x_2266_ = 1;
    v___x_2267_ = lean_task_bind(v___x_2265_, v___f_2262_, v___x_2261_, v___x_2266_);
    v___x_2268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    v___x_2269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2268_);
    v___x_2270_ = 0;
    v___x_2271_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2261_,
        v___x_2270_,
        v___x_2269_,
        v___f_2263_,
    );
    return v___x_2271_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__7___boxed(
    mut v___f_2272_: *mut crate::leanh::LeanObject,
    mut v___x_2273_: *mut crate::leanh::LeanObject,
    mut v___f_2274_: *mut crate::leanh::LeanObject,
    mut v___f_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Std_Async_Signal_Waiter_selector___lam__7(
        v___f_2272_,
        v___x_2273_,
        v___f_2274_,
        v___f_2275_,
    );
    return v_res_2277_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__8(
    mut v___x_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2280_, 0, v___x_2278_);
    return v___x_2280_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__8___boxed(
    mut v___x_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___x_2281_);
    return v_res_2283_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__9(
    mut v_waiter_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___f_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_unused_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2287_) == 0 {
                    v_a_2292_ = crate::leanh::lean_ctor_get(v_a_2287_, 0);
                    crate::leanh::lean_inc(v_a_2292_);
                    crate::leanh::lean_dec_ref_known(v_a_2287_, 1);
                    v_a_2290_ = v_a_2292_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_2303_ = (!crate::leanh::lean_is_exclusive(v_a_2287_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v_unused_2304_ = crate::leanh::lean_ctor_get(v_a_2287_, 0);
                        crate::leanh::lean_dec(v_unused_2304_);
                        v___x_2294_ = v_a_2287_;
                        v_isShared_2295_ = v_isSharedCheck_2303_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2287_);
                        v___x_2294_ = crate::leanh::lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2303_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2291_, 0, v_a_2290_);
                return v___x_2291_;
            }
            2 => {
                v___f_2296_ = l_Std_Async_Signal_Waiter_selector___lam__9___closed__0;
                v___x_2297_ =
                    l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(
                        v_waiter_2286_,
                        v___f_2296_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2297_) == 0 {
                    v_a_2298_ = crate::leanh::lean_ctor_get(v___x_2297_, 0);
                    crate::leanh::lean_inc(v_a_2298_);
                    crate::leanh::lean_dec_ref_known(v___x_2297_, 1);
                    if v_isShared_2295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2294_, 0, v_a_2298_);
                        v___x_2300_ = v___x_2294_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2298_);
                        v___x_2300_ = v_reuseFailAlloc_2301_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2294_);
                    v_a_2302_ = crate::leanh::lean_ctor_get(v___x_2297_, 0);
                    crate::leanh::lean_inc(v_a_2302_);
                    crate::leanh::lean_dec_ref_known(v___x_2297_, 1);
                    v_a_2290_ = v_a_2302_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_2300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__9___boxed(
    mut v_waiter_2305_: *mut crate::leanh::LeanObject,
    mut v_a_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2308_ = l_Std_Async_Signal_Waiter_selector___lam__9(v_waiter_2305_, v_a_2306_);
    crate::leanh::lean_dec_ref(v_waiter_2305_);
    return v_res_2308_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__10(
    mut v___f_2311_: *mut crate::leanh::LeanObject,
    mut v___x_2312_: *mut crate::leanh::LeanObject,
    mut v_x_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_a_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2313_) == 0 {
                    crate::leanh::lean_dec(v___x_2312_);
                    crate::leanh::lean_dec_ref(v___f_2311_);
                    v_a_2315_ = crate::leanh::lean_ctor_get(v_x_2313_, 0);
                    v_isSharedCheck_2323_ = (!crate::leanh::lean_is_exclusive(v_x_2313_)) as u8;
                    if v_isSharedCheck_2323_ == 0 {
                        v___x_2317_ = v_x_2313_;
                        v_isShared_2318_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2315_);
                        crate::leanh::lean_dec(v_x_2313_);
                        v___x_2317_ = crate::leanh::lean_box(0);
                        v_isShared_2318_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2324_ = crate::leanh::lean_ctor_get(v_x_2313_, 0);
                    crate::leanh::lean_inc(v_a_2324_);
                    crate::leanh::lean_dec_ref_known(v_x_2313_, 1);
                    v___x_2325_ = 0;
                    v___x_2326_ =
                        lean_io_map_task(v___f_2311_, v_a_2324_, v___x_2312_, v___x_2325_);
                    crate::leanh::lean_dec_ref(v___x_2326_);
                    v___x_2327_ = l_Std_Async_Signal_Waiter_selector___lam__10___closed__0;
                    return v___x_2327_;
                }
            }
            1 => {
                if v_isShared_2318_ == 0 {
                    v___x_2320_ = v___x_2317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2315_);
                    v___x_2320_ = v_reuseFailAlloc_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2321_, 0, v___x_2320_);
                return v___x_2321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__10___boxed(
    mut v___f_2328_: *mut crate::leanh::LeanObject,
    mut v___x_2329_: *mut crate::leanh::LeanObject,
    mut v_x_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ = l_Std_Async_Signal_Waiter_selector___lam__10(v___f_2328_, v___x_2329_, v_x_2330_);
    return v_res_2332_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__11(
    mut v___f_2333_: *mut crate::leanh::LeanObject,
    mut v___x_2334_: *mut crate::leanh::LeanObject,
    mut v_waiter_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = crate::leanh::lean_apply_1(v___f_2333_, crate::leanh::lean_box(0));
    v___f_2338_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__9___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2338_, 0, v_waiter_2335_);
    crate::leanh::lean_inc(v___x_2334_);
    v___f_2339_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__10___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2339_, 0, v___f_2338_);
    crate::leanh::lean_closure_set(v___f_2339_, 1, v___x_2334_);
    v___x_2340_ = 0;
    v___x_2341_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2334_,
        v___x_2340_,
        v___x_2337_,
        v___f_2339_,
    );
    return v___x_2341_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__11___boxed(
    mut v___f_2342_: *mut crate::leanh::LeanObject,
    mut v___x_2343_: *mut crate::leanh::LeanObject,
    mut v_waiter_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ =
        l_Std_Async_Signal_Waiter_selector___lam__11(v___f_2342_, v___x_2343_, v_waiter_2344_);
    return v_res_2346_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector(
    mut v_s_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_s_2349_, 2);
    v___f_2350_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2350_, 0, v_s_2349_);
    v___f_2351_ = l_Std_Async_Signal_Waiter_selector___closed__0;
    v___f_2352_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2352_, 0, v___f_2351_);
    crate::leanh::lean_closure_set(v___f_2352_, 1, v_s_2349_);
    v___f_2353_ = l_Std_Async_Signal_Waiter_selector___closed__1;
    v___f_2354_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__5___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2354_, 0, v_s_2349_);
    crate::leanh::lean_inc_ref(v___f_2354_);
    v___f_2355_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2355_, 0, v___f_2354_);
    v___x_2356_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_2357_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2357_, 0, v___x_2356_);
    crate::leanh::lean_closure_set(v___f_2357_, 1, v___f_2352_);
    v___f_2358_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__7___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2358_, 0, v___f_2355_);
    crate::leanh::lean_closure_set(v___f_2358_, 1, v___x_2356_);
    crate::leanh::lean_closure_set(v___f_2358_, 2, v___f_2353_);
    crate::leanh::lean_closure_set(v___f_2358_, 3, v___f_2357_);
    v___f_2359_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2359_, 0, v___f_2354_);
    crate::leanh::lean_closure_set(v___f_2359_, 1, v___x_2356_);
    v___x_2360_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2360_, 0, v___f_2358_);
    crate::leanh::lean_ctor_set(v___x_2360_, 1, v___f_2359_);
    crate::leanh::lean_ctor_set(v___x_2360_, 2, v___f_2350_);
    return v___x_2360_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_Signal(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Std_Internal_UV_Signal(builtin);
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
pub unsafe fn meta_initialize_Std_Async_Signal(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_Signal(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Std_Internal_UV_Signal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Signal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_Signal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Async_Signal(builtin);
}
