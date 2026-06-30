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
pub static l_Std_Async_instReprSignal_repr___closed__0_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Async_instReprSignal_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__2_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Async_instReprSignal_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__4_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 113, 117, 105, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__6_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 114, 97, 112, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__8_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 97, 98, 114, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__10_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 117, 115, 114, 49, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__12_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 117, 115, 114, 50, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__14_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 97, 108, 114, 109, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__15_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__16_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 101, 114, 109, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__18_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 99, 104, 108, 100, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__19_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__20_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 99, 111, 110, 116, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__22_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 115, 116, 112, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__23_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__24_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 116, 105, 110, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__25_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__26_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 116, 116, 111, 117, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__27_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__26_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__28_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Async_instReprSignal_repr___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__29_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__30_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 120, 99, 112, 117, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__31_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__30_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__32_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 120, 102, 115, 122, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__33_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__32_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__34_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 118, 116, 97, 108, 114, 109, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__35_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__34_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__36_value: leanh::LeanStringObject<25> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 112, 114, 111, 102, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__37_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__36_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__38_value: leanh::LeanStringObject<26> =
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
            83, 116, 100, 46, 65, 115, 121, 110, 99, 46, 83, 105, 103, 110, 97, 108, 46, 115, 105,
            103, 119, 105, 110, 99, 104, 0,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__39_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__38_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__40_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Async_instReprSignal_repr___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__41_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__40_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__42_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Async_instReprSignal_repr___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instReprSignal_repr___closed__43_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__42_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_instReprSignal_repr___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal_repr___closed__43_value)
        as *mut leanh::LeanObject;
static mut l_Std_Async_instReprSignal_repr___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_instReprSignal_repr___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Async_instReprSignal_repr___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_instReprSignal_repr___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_instReprSignal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Async_instReprSignal_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_instReprSignal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_instReprSignal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instReprSignal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_instBEqSignal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Async_instBEqSignal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_instBEqSignal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instBEqSignal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Async_instBEqSignal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_instBEqSignal___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20: u32 = 0;
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21: u32 = 0;
pub static l_Std_Async_Signal_Waiter_wait___closed__0_value: leanh::LeanStringObject<49> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Async_Signal_Waiter_wait___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_wait___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_wait___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Signal_Waiter_wait___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Signal_Waiter_wait___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_Signal_Waiter_wait___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_wait___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value:
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
static mut l_Std_Async_Signal_Waiter_selector___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value:
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
static mut l_Std_Async_Signal_Waiter_selector___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value:
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
    m_fun: l_Std_Async_Signal_Waiter_selector___lam__8___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__9___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__9___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Async_Signal_Waiter_selector___lam__10___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___lam__10___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_Signal_Waiter_selector___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Signal_Waiter_selector___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Signal_Waiter_selector___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_Signal_Waiter_selector___lam__3 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Signal_Waiter_selector___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_Signal_Waiter_selector___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Async_Signal_ctorIdx(mut v_x_1181_: u8) -> *mut leanh::LeanObject {
    match v_x_1181_ {
        0 => {
            let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1182_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1182_;
        }
        1 => {
            let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1183_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1183_;
        }
        2 => {
            let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1184_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1184_;
        }
        3 => {
            let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1185_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1185_;
        }
        4 => {
            let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1186_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1186_;
        }
        5 => {
            let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1187_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1187_;
        }
        6 => {
            let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1188_ = leanh::lean_unsigned_to_nat(6);
            return v___x_1188_;
        }
        7 => {
            let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1189_ = leanh::lean_unsigned_to_nat(7);
            return v___x_1189_;
        }
        8 => {
            let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1190_ = leanh::lean_unsigned_to_nat(8);
            return v___x_1190_;
        }
        9 => {
            let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1191_ = leanh::lean_unsigned_to_nat(9);
            return v___x_1191_;
        }
        10 => {
            let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1192_ = leanh::lean_unsigned_to_nat(10);
            return v___x_1192_;
        }
        11 => {
            let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1193_ = leanh::lean_unsigned_to_nat(11);
            return v___x_1193_;
        }
        12 => {
            let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1194_ = leanh::lean_unsigned_to_nat(12);
            return v___x_1194_;
        }
        13 => {
            let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1195_ = leanh::lean_unsigned_to_nat(13);
            return v___x_1195_;
        }
        14 => {
            let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1196_ = leanh::lean_unsigned_to_nat(14);
            return v___x_1196_;
        }
        15 => {
            let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1197_ = leanh::lean_unsigned_to_nat(15);
            return v___x_1197_;
        }
        16 => {
            let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1198_ = leanh::lean_unsigned_to_nat(16);
            return v___x_1198_;
        }
        17 => {
            let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1199_ = leanh::lean_unsigned_to_nat(17);
            return v___x_1199_;
        }
        18 => {
            let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1200_ = leanh::lean_unsigned_to_nat(18);
            return v___x_1200_;
        }
        19 => {
            let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1201_ = leanh::lean_unsigned_to_nat(19);
            return v___x_1201_;
        }
        20 => {
            let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1202_ = leanh::lean_unsigned_to_nat(20);
            return v___x_1202_;
        }
        _ => {
            let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1203_ = leanh::lean_unsigned_to_nat(21);
            return v___x_1203_;
        }
    }
}
pub unsafe fn l_Std_Async_Signal_ctorIdx___boxed(
    mut v_x_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1205_: u8 = 0;
    let mut v_res_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1205_ = (leanh::lean_unbox(v_x_1204_) as u8);
    v_res_1206_ = l_Std_Async_Signal_ctorIdx(v_x_boxed_1205_);
    return v_res_1206_;
}
pub unsafe fn l_Std_Async_Signal_toCtorIdx(mut v_x_1207_: u8) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Std_Async_Signal_ctorIdx(v_x_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Std_Async_Signal_toCtorIdx___boxed(
    mut v_x_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1210_: u8 = 0;
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1210_ = (leanh::lean_unbox(v_x_1209_) as u8);
    v_res_1211_ = l_Std_Async_Signal_toCtorIdx(v_x_4__boxed_1210_);
    return v_res_1211_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim___redArg(
    mut v_k_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1212_);
    return v_k_1212_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim___redArg___boxed(
    mut v_k_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1214_ = l_Std_Async_Signal_ctorElim___redArg(v_k_1213_);
    leanh::lean_dec(v_k_1213_);
    return v_res_1214_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim(
    mut v_motive_1215_: *mut leanh::LeanObject,
    mut v_ctorIdx_1216_: *mut leanh::LeanObject,
    mut v_t_1217_: u8,
    mut v_h_1218_: *mut leanh::LeanObject,
    mut v_k_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1219_);
    return v_k_1219_;
}
pub unsafe fn l_Std_Async_Signal_ctorElim___boxed(
    mut v_motive_1220_: *mut leanh::LeanObject,
    mut v_ctorIdx_1221_: *mut leanh::LeanObject,
    mut v_t_1222_: *mut leanh::LeanObject,
    mut v_h_1223_: *mut leanh::LeanObject,
    mut v_k_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1225_: u8 = 0;
    let mut v_res_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1225_ = (leanh::lean_unbox(v_t_1222_) as u8);
    v_res_1226_ = l_Std_Async_Signal_ctorElim(
        v_motive_1220_,
        v_ctorIdx_1221_,
        v_t_boxed_1225_,
        v_h_1223_,
        v_k_1224_,
    );
    leanh::lean_dec(v_k_1224_);
    leanh::lean_dec(v_ctorIdx_1221_);
    return v_res_1226_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim___redArg(
    mut v_sighup_1227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sighup_1227_);
    return v_sighup_1227_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim___redArg___boxed(
    mut v_sighup_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Std_Async_Signal_sighup_elim___redArg(v_sighup_1228_);
    leanh::lean_dec(v_sighup_1228_);
    return v_res_1229_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim(
    mut v_motive_1230_: *mut leanh::LeanObject,
    mut v_t_1231_: u8,
    mut v_h_1232_: *mut leanh::LeanObject,
    mut v_sighup_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sighup_1233_);
    return v_sighup_1233_;
}
pub unsafe fn l_Std_Async_Signal_sighup_elim___boxed(
    mut v_motive_1234_: *mut leanh::LeanObject,
    mut v_t_1235_: *mut leanh::LeanObject,
    mut v_h_1236_: *mut leanh::LeanObject,
    mut v_sighup_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1238_: u8 = 0;
    let mut v_res_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1238_ = (leanh::lean_unbox(v_t_1235_) as u8);
    v_res_1239_ =
        l_Std_Async_Signal_sighup_elim(v_motive_1234_, v_t_boxed_1238_, v_h_1236_, v_sighup_1237_);
    leanh::lean_dec(v_sighup_1237_);
    return v_res_1239_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim___redArg(
    mut v_sigint_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigint_1240_);
    return v_sigint_1240_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim___redArg___boxed(
    mut v_sigint_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_Std_Async_Signal_sigint_elim___redArg(v_sigint_1241_);
    leanh::lean_dec(v_sigint_1241_);
    return v_res_1242_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim(
    mut v_motive_1243_: *mut leanh::LeanObject,
    mut v_t_1244_: u8,
    mut v_h_1245_: *mut leanh::LeanObject,
    mut v_sigint_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigint_1246_);
    return v_sigint_1246_;
}
pub unsafe fn l_Std_Async_Signal_sigint_elim___boxed(
    mut v_motive_1247_: *mut leanh::LeanObject,
    mut v_t_1248_: *mut leanh::LeanObject,
    mut v_h_1249_: *mut leanh::LeanObject,
    mut v_sigint_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1251_: u8 = 0;
    let mut v_res_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1251_ = (leanh::lean_unbox(v_t_1248_) as u8);
    v_res_1252_ =
        l_Std_Async_Signal_sigint_elim(v_motive_1247_, v_t_boxed_1251_, v_h_1249_, v_sigint_1250_);
    leanh::lean_dec(v_sigint_1250_);
    return v_res_1252_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim___redArg(
    mut v_sigquit_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigquit_1253_);
    return v_sigquit_1253_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim___redArg___boxed(
    mut v_sigquit_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_Std_Async_Signal_sigquit_elim___redArg(v_sigquit_1254_);
    leanh::lean_dec(v_sigquit_1254_);
    return v_res_1255_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim(
    mut v_motive_1256_: *mut leanh::LeanObject,
    mut v_t_1257_: u8,
    mut v_h_1258_: *mut leanh::LeanObject,
    mut v_sigquit_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigquit_1259_);
    return v_sigquit_1259_;
}
pub unsafe fn l_Std_Async_Signal_sigquit_elim___boxed(
    mut v_motive_1260_: *mut leanh::LeanObject,
    mut v_t_1261_: *mut leanh::LeanObject,
    mut v_h_1262_: *mut leanh::LeanObject,
    mut v_sigquit_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1264_: u8 = 0;
    let mut v_res_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1264_ = (leanh::lean_unbox(v_t_1261_) as u8);
    v_res_1265_ = l_Std_Async_Signal_sigquit_elim(
        v_motive_1260_,
        v_t_boxed_1264_,
        v_h_1262_,
        v_sigquit_1263_,
    );
    leanh::lean_dec(v_sigquit_1263_);
    return v_res_1265_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim___redArg(
    mut v_sigtrap_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigtrap_1266_);
    return v_sigtrap_1266_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim___redArg___boxed(
    mut v_sigtrap_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Std_Async_Signal_sigtrap_elim___redArg(v_sigtrap_1267_);
    leanh::lean_dec(v_sigtrap_1267_);
    return v_res_1268_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim(
    mut v_motive_1269_: *mut leanh::LeanObject,
    mut v_t_1270_: u8,
    mut v_h_1271_: *mut leanh::LeanObject,
    mut v_sigtrap_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigtrap_1272_);
    return v_sigtrap_1272_;
}
pub unsafe fn l_Std_Async_Signal_sigtrap_elim___boxed(
    mut v_motive_1273_: *mut leanh::LeanObject,
    mut v_t_1274_: *mut leanh::LeanObject,
    mut v_h_1275_: *mut leanh::LeanObject,
    mut v_sigtrap_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1277_: u8 = 0;
    let mut v_res_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1277_ = (leanh::lean_unbox(v_t_1274_) as u8);
    v_res_1278_ = l_Std_Async_Signal_sigtrap_elim(
        v_motive_1273_,
        v_t_boxed_1277_,
        v_h_1275_,
        v_sigtrap_1276_,
    );
    leanh::lean_dec(v_sigtrap_1276_);
    return v_res_1278_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim___redArg(
    mut v_sigabrt_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigabrt_1279_);
    return v_sigabrt_1279_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim___redArg___boxed(
    mut v_sigabrt_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Std_Async_Signal_sigabrt_elim___redArg(v_sigabrt_1280_);
    leanh::lean_dec(v_sigabrt_1280_);
    return v_res_1281_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim(
    mut v_motive_1282_: *mut leanh::LeanObject,
    mut v_t_1283_: u8,
    mut v_h_1284_: *mut leanh::LeanObject,
    mut v_sigabrt_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigabrt_1285_);
    return v_sigabrt_1285_;
}
pub unsafe fn l_Std_Async_Signal_sigabrt_elim___boxed(
    mut v_motive_1286_: *mut leanh::LeanObject,
    mut v_t_1287_: *mut leanh::LeanObject,
    mut v_h_1288_: *mut leanh::LeanObject,
    mut v_sigabrt_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1290_: u8 = 0;
    let mut v_res_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1290_ = (leanh::lean_unbox(v_t_1287_) as u8);
    v_res_1291_ = l_Std_Async_Signal_sigabrt_elim(
        v_motive_1286_,
        v_t_boxed_1290_,
        v_h_1288_,
        v_sigabrt_1289_,
    );
    leanh::lean_dec(v_sigabrt_1289_);
    return v_res_1291_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim___redArg(
    mut v_sigusr1_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigusr1_1292_);
    return v_sigusr1_1292_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim___redArg___boxed(
    mut v_sigusr1_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_Async_Signal_sigusr1_elim___redArg(v_sigusr1_1293_);
    leanh::lean_dec(v_sigusr1_1293_);
    return v_res_1294_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim(
    mut v_motive_1295_: *mut leanh::LeanObject,
    mut v_t_1296_: u8,
    mut v_h_1297_: *mut leanh::LeanObject,
    mut v_sigusr1_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigusr1_1298_);
    return v_sigusr1_1298_;
}
pub unsafe fn l_Std_Async_Signal_sigusr1_elim___boxed(
    mut v_motive_1299_: *mut leanh::LeanObject,
    mut v_t_1300_: *mut leanh::LeanObject,
    mut v_h_1301_: *mut leanh::LeanObject,
    mut v_sigusr1_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1303_: u8 = 0;
    let mut v_res_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1303_ = (leanh::lean_unbox(v_t_1300_) as u8);
    v_res_1304_ = l_Std_Async_Signal_sigusr1_elim(
        v_motive_1299_,
        v_t_boxed_1303_,
        v_h_1301_,
        v_sigusr1_1302_,
    );
    leanh::lean_dec(v_sigusr1_1302_);
    return v_res_1304_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim___redArg(
    mut v_sigusr2_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigusr2_1305_);
    return v_sigusr2_1305_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim___redArg___boxed(
    mut v_sigusr2_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Std_Async_Signal_sigusr2_elim___redArg(v_sigusr2_1306_);
    leanh::lean_dec(v_sigusr2_1306_);
    return v_res_1307_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim(
    mut v_motive_1308_: *mut leanh::LeanObject,
    mut v_t_1309_: u8,
    mut v_h_1310_: *mut leanh::LeanObject,
    mut v_sigusr2_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigusr2_1311_);
    return v_sigusr2_1311_;
}
pub unsafe fn l_Std_Async_Signal_sigusr2_elim___boxed(
    mut v_motive_1312_: *mut leanh::LeanObject,
    mut v_t_1313_: *mut leanh::LeanObject,
    mut v_h_1314_: *mut leanh::LeanObject,
    mut v_sigusr2_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1316_: u8 = 0;
    let mut v_res_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1316_ = (leanh::lean_unbox(v_t_1313_) as u8);
    v_res_1317_ = l_Std_Async_Signal_sigusr2_elim(
        v_motive_1312_,
        v_t_boxed_1316_,
        v_h_1314_,
        v_sigusr2_1315_,
    );
    leanh::lean_dec(v_sigusr2_1315_);
    return v_res_1317_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim___redArg(
    mut v_sigalrm_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigalrm_1318_);
    return v_sigalrm_1318_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim___redArg___boxed(
    mut v_sigalrm_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Std_Async_Signal_sigalrm_elim___redArg(v_sigalrm_1319_);
    leanh::lean_dec(v_sigalrm_1319_);
    return v_res_1320_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim(
    mut v_motive_1321_: *mut leanh::LeanObject,
    mut v_t_1322_: u8,
    mut v_h_1323_: *mut leanh::LeanObject,
    mut v_sigalrm_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigalrm_1324_);
    return v_sigalrm_1324_;
}
pub unsafe fn l_Std_Async_Signal_sigalrm_elim___boxed(
    mut v_motive_1325_: *mut leanh::LeanObject,
    mut v_t_1326_: *mut leanh::LeanObject,
    mut v_h_1327_: *mut leanh::LeanObject,
    mut v_sigalrm_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1329_ = (leanh::lean_unbox(v_t_1326_) as u8);
    v_res_1330_ = l_Std_Async_Signal_sigalrm_elim(
        v_motive_1325_,
        v_t_boxed_1329_,
        v_h_1327_,
        v_sigalrm_1328_,
    );
    leanh::lean_dec(v_sigalrm_1328_);
    return v_res_1330_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim___redArg(
    mut v_sigterm_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigterm_1331_);
    return v_sigterm_1331_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim___redArg___boxed(
    mut v_sigterm_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_Std_Async_Signal_sigterm_elim___redArg(v_sigterm_1332_);
    leanh::lean_dec(v_sigterm_1332_);
    return v_res_1333_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim(
    mut v_motive_1334_: *mut leanh::LeanObject,
    mut v_t_1335_: u8,
    mut v_h_1336_: *mut leanh::LeanObject,
    mut v_sigterm_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigterm_1337_);
    return v_sigterm_1337_;
}
pub unsafe fn l_Std_Async_Signal_sigterm_elim___boxed(
    mut v_motive_1338_: *mut leanh::LeanObject,
    mut v_t_1339_: *mut leanh::LeanObject,
    mut v_h_1340_: *mut leanh::LeanObject,
    mut v_sigterm_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1342_: u8 = 0;
    let mut v_res_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1342_ = (leanh::lean_unbox(v_t_1339_) as u8);
    v_res_1343_ = l_Std_Async_Signal_sigterm_elim(
        v_motive_1338_,
        v_t_boxed_1342_,
        v_h_1340_,
        v_sigterm_1341_,
    );
    leanh::lean_dec(v_sigterm_1341_);
    return v_res_1343_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim___redArg(
    mut v_sigchld_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigchld_1344_);
    return v_sigchld_1344_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim___redArg___boxed(
    mut v_sigchld_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Std_Async_Signal_sigchld_elim___redArg(v_sigchld_1345_);
    leanh::lean_dec(v_sigchld_1345_);
    return v_res_1346_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim(
    mut v_motive_1347_: *mut leanh::LeanObject,
    mut v_t_1348_: u8,
    mut v_h_1349_: *mut leanh::LeanObject,
    mut v_sigchld_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigchld_1350_);
    return v_sigchld_1350_;
}
pub unsafe fn l_Std_Async_Signal_sigchld_elim___boxed(
    mut v_motive_1351_: *mut leanh::LeanObject,
    mut v_t_1352_: *mut leanh::LeanObject,
    mut v_h_1353_: *mut leanh::LeanObject,
    mut v_sigchld_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1355_: u8 = 0;
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1355_ = (leanh::lean_unbox(v_t_1352_) as u8);
    v_res_1356_ = l_Std_Async_Signal_sigchld_elim(
        v_motive_1351_,
        v_t_boxed_1355_,
        v_h_1353_,
        v_sigchld_1354_,
    );
    leanh::lean_dec(v_sigchld_1354_);
    return v_res_1356_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim___redArg(
    mut v_sigcont_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigcont_1357_);
    return v_sigcont_1357_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim___redArg___boxed(
    mut v_sigcont_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Std_Async_Signal_sigcont_elim___redArg(v_sigcont_1358_);
    leanh::lean_dec(v_sigcont_1358_);
    return v_res_1359_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim(
    mut v_motive_1360_: *mut leanh::LeanObject,
    mut v_t_1361_: u8,
    mut v_h_1362_: *mut leanh::LeanObject,
    mut v_sigcont_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigcont_1363_);
    return v_sigcont_1363_;
}
pub unsafe fn l_Std_Async_Signal_sigcont_elim___boxed(
    mut v_motive_1364_: *mut leanh::LeanObject,
    mut v_t_1365_: *mut leanh::LeanObject,
    mut v_h_1366_: *mut leanh::LeanObject,
    mut v_sigcont_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1368_: u8 = 0;
    let mut v_res_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1368_ = (leanh::lean_unbox(v_t_1365_) as u8);
    v_res_1369_ = l_Std_Async_Signal_sigcont_elim(
        v_motive_1364_,
        v_t_boxed_1368_,
        v_h_1366_,
        v_sigcont_1367_,
    );
    leanh::lean_dec(v_sigcont_1367_);
    return v_res_1369_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim___redArg(
    mut v_sigtstp_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigtstp_1370_);
    return v_sigtstp_1370_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim___redArg___boxed(
    mut v_sigtstp_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Std_Async_Signal_sigtstp_elim___redArg(v_sigtstp_1371_);
    leanh::lean_dec(v_sigtstp_1371_);
    return v_res_1372_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim(
    mut v_motive_1373_: *mut leanh::LeanObject,
    mut v_t_1374_: u8,
    mut v_h_1375_: *mut leanh::LeanObject,
    mut v_sigtstp_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigtstp_1376_);
    return v_sigtstp_1376_;
}
pub unsafe fn l_Std_Async_Signal_sigtstp_elim___boxed(
    mut v_motive_1377_: *mut leanh::LeanObject,
    mut v_t_1378_: *mut leanh::LeanObject,
    mut v_h_1379_: *mut leanh::LeanObject,
    mut v_sigtstp_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1381_: u8 = 0;
    let mut v_res_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1381_ = (leanh::lean_unbox(v_t_1378_) as u8);
    v_res_1382_ = l_Std_Async_Signal_sigtstp_elim(
        v_motive_1377_,
        v_t_boxed_1381_,
        v_h_1379_,
        v_sigtstp_1380_,
    );
    leanh::lean_dec(v_sigtstp_1380_);
    return v_res_1382_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim___redArg(
    mut v_sigttin_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigttin_1383_);
    return v_sigttin_1383_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim___redArg___boxed(
    mut v_sigttin_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Std_Async_Signal_sigttin_elim___redArg(v_sigttin_1384_);
    leanh::lean_dec(v_sigttin_1384_);
    return v_res_1385_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim(
    mut v_motive_1386_: *mut leanh::LeanObject,
    mut v_t_1387_: u8,
    mut v_h_1388_: *mut leanh::LeanObject,
    mut v_sigttin_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigttin_1389_);
    return v_sigttin_1389_;
}
pub unsafe fn l_Std_Async_Signal_sigttin_elim___boxed(
    mut v_motive_1390_: *mut leanh::LeanObject,
    mut v_t_1391_: *mut leanh::LeanObject,
    mut v_h_1392_: *mut leanh::LeanObject,
    mut v_sigttin_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1394_: u8 = 0;
    let mut v_res_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1394_ = (leanh::lean_unbox(v_t_1391_) as u8);
    v_res_1395_ = l_Std_Async_Signal_sigttin_elim(
        v_motive_1390_,
        v_t_boxed_1394_,
        v_h_1392_,
        v_sigttin_1393_,
    );
    leanh::lean_dec(v_sigttin_1393_);
    return v_res_1395_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim___redArg(
    mut v_sigttou_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigttou_1396_);
    return v_sigttou_1396_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim___redArg___boxed(
    mut v_sigttou_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Std_Async_Signal_sigttou_elim___redArg(v_sigttou_1397_);
    leanh::lean_dec(v_sigttou_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim(
    mut v_motive_1399_: *mut leanh::LeanObject,
    mut v_t_1400_: u8,
    mut v_h_1401_: *mut leanh::LeanObject,
    mut v_sigttou_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigttou_1402_);
    return v_sigttou_1402_;
}
pub unsafe fn l_Std_Async_Signal_sigttou_elim___boxed(
    mut v_motive_1403_: *mut leanh::LeanObject,
    mut v_t_1404_: *mut leanh::LeanObject,
    mut v_h_1405_: *mut leanh::LeanObject,
    mut v_sigttou_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1407_: u8 = 0;
    let mut v_res_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1407_ = (leanh::lean_unbox(v_t_1404_) as u8);
    v_res_1408_ = l_Std_Async_Signal_sigttou_elim(
        v_motive_1403_,
        v_t_boxed_1407_,
        v_h_1405_,
        v_sigttou_1406_,
    );
    leanh::lean_dec(v_sigttou_1406_);
    return v_res_1408_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim___redArg(
    mut v_sigurg_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigurg_1409_);
    return v_sigurg_1409_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim___redArg___boxed(
    mut v_sigurg_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Std_Async_Signal_sigurg_elim___redArg(v_sigurg_1410_);
    leanh::lean_dec(v_sigurg_1410_);
    return v_res_1411_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim(
    mut v_motive_1412_: *mut leanh::LeanObject,
    mut v_t_1413_: u8,
    mut v_h_1414_: *mut leanh::LeanObject,
    mut v_sigurg_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigurg_1415_);
    return v_sigurg_1415_;
}
pub unsafe fn l_Std_Async_Signal_sigurg_elim___boxed(
    mut v_motive_1416_: *mut leanh::LeanObject,
    mut v_t_1417_: *mut leanh::LeanObject,
    mut v_h_1418_: *mut leanh::LeanObject,
    mut v_sigurg_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1420_: u8 = 0;
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1420_ = (leanh::lean_unbox(v_t_1417_) as u8);
    v_res_1421_ =
        l_Std_Async_Signal_sigurg_elim(v_motive_1416_, v_t_boxed_1420_, v_h_1418_, v_sigurg_1419_);
    leanh::lean_dec(v_sigurg_1419_);
    return v_res_1421_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim___redArg(
    mut v_sigxcpu_1422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigxcpu_1422_);
    return v_sigxcpu_1422_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim___redArg___boxed(
    mut v_sigxcpu_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Std_Async_Signal_sigxcpu_elim___redArg(v_sigxcpu_1423_);
    leanh::lean_dec(v_sigxcpu_1423_);
    return v_res_1424_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim(
    mut v_motive_1425_: *mut leanh::LeanObject,
    mut v_t_1426_: u8,
    mut v_h_1427_: *mut leanh::LeanObject,
    mut v_sigxcpu_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigxcpu_1428_);
    return v_sigxcpu_1428_;
}
pub unsafe fn l_Std_Async_Signal_sigxcpu_elim___boxed(
    mut v_motive_1429_: *mut leanh::LeanObject,
    mut v_t_1430_: *mut leanh::LeanObject,
    mut v_h_1431_: *mut leanh::LeanObject,
    mut v_sigxcpu_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1433_: u8 = 0;
    let mut v_res_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1433_ = (leanh::lean_unbox(v_t_1430_) as u8);
    v_res_1434_ = l_Std_Async_Signal_sigxcpu_elim(
        v_motive_1429_,
        v_t_boxed_1433_,
        v_h_1431_,
        v_sigxcpu_1432_,
    );
    leanh::lean_dec(v_sigxcpu_1432_);
    return v_res_1434_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim___redArg(
    mut v_sigxfsz_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigxfsz_1435_);
    return v_sigxfsz_1435_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim___redArg___boxed(
    mut v_sigxfsz_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Std_Async_Signal_sigxfsz_elim___redArg(v_sigxfsz_1436_);
    leanh::lean_dec(v_sigxfsz_1436_);
    return v_res_1437_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim(
    mut v_motive_1438_: *mut leanh::LeanObject,
    mut v_t_1439_: u8,
    mut v_h_1440_: *mut leanh::LeanObject,
    mut v_sigxfsz_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigxfsz_1441_);
    return v_sigxfsz_1441_;
}
pub unsafe fn l_Std_Async_Signal_sigxfsz_elim___boxed(
    mut v_motive_1442_: *mut leanh::LeanObject,
    mut v_t_1443_: *mut leanh::LeanObject,
    mut v_h_1444_: *mut leanh::LeanObject,
    mut v_sigxfsz_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1446_: u8 = 0;
    let mut v_res_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1446_ = (leanh::lean_unbox(v_t_1443_) as u8);
    v_res_1447_ = l_Std_Async_Signal_sigxfsz_elim(
        v_motive_1442_,
        v_t_boxed_1446_,
        v_h_1444_,
        v_sigxfsz_1445_,
    );
    leanh::lean_dec(v_sigxfsz_1445_);
    return v_res_1447_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim___redArg(
    mut v_sigvtalrm_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigvtalrm_1448_);
    return v_sigvtalrm_1448_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim___redArg___boxed(
    mut v_sigvtalrm_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Std_Async_Signal_sigvtalrm_elim___redArg(v_sigvtalrm_1449_);
    leanh::lean_dec(v_sigvtalrm_1449_);
    return v_res_1450_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim(
    mut v_motive_1451_: *mut leanh::LeanObject,
    mut v_t_1452_: u8,
    mut v_h_1453_: *mut leanh::LeanObject,
    mut v_sigvtalrm_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigvtalrm_1454_);
    return v_sigvtalrm_1454_;
}
pub unsafe fn l_Std_Async_Signal_sigvtalrm_elim___boxed(
    mut v_motive_1455_: *mut leanh::LeanObject,
    mut v_t_1456_: *mut leanh::LeanObject,
    mut v_h_1457_: *mut leanh::LeanObject,
    mut v_sigvtalrm_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1459_: u8 = 0;
    let mut v_res_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1459_ = (leanh::lean_unbox(v_t_1456_) as u8);
    v_res_1460_ = l_Std_Async_Signal_sigvtalrm_elim(
        v_motive_1455_,
        v_t_boxed_1459_,
        v_h_1457_,
        v_sigvtalrm_1458_,
    );
    leanh::lean_dec(v_sigvtalrm_1458_);
    return v_res_1460_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim___redArg(
    mut v_sigprof_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigprof_1461_);
    return v_sigprof_1461_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim___redArg___boxed(
    mut v_sigprof_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Std_Async_Signal_sigprof_elim___redArg(v_sigprof_1462_);
    leanh::lean_dec(v_sigprof_1462_);
    return v_res_1463_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim(
    mut v_motive_1464_: *mut leanh::LeanObject,
    mut v_t_1465_: u8,
    mut v_h_1466_: *mut leanh::LeanObject,
    mut v_sigprof_1467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigprof_1467_);
    return v_sigprof_1467_;
}
pub unsafe fn l_Std_Async_Signal_sigprof_elim___boxed(
    mut v_motive_1468_: *mut leanh::LeanObject,
    mut v_t_1469_: *mut leanh::LeanObject,
    mut v_h_1470_: *mut leanh::LeanObject,
    mut v_sigprof_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1472_: u8 = 0;
    let mut v_res_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1472_ = (leanh::lean_unbox(v_t_1469_) as u8);
    v_res_1473_ = l_Std_Async_Signal_sigprof_elim(
        v_motive_1468_,
        v_t_boxed_1472_,
        v_h_1470_,
        v_sigprof_1471_,
    );
    leanh::lean_dec(v_sigprof_1471_);
    return v_res_1473_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim___redArg(
    mut v_sigwinch_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigwinch_1474_);
    return v_sigwinch_1474_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim___redArg___boxed(
    mut v_sigwinch_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1476_ = l_Std_Async_Signal_sigwinch_elim___redArg(v_sigwinch_1475_);
    leanh::lean_dec(v_sigwinch_1475_);
    return v_res_1476_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim(
    mut v_motive_1477_: *mut leanh::LeanObject,
    mut v_t_1478_: u8,
    mut v_h_1479_: *mut leanh::LeanObject,
    mut v_sigwinch_1480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigwinch_1480_);
    return v_sigwinch_1480_;
}
pub unsafe fn l_Std_Async_Signal_sigwinch_elim___boxed(
    mut v_motive_1481_: *mut leanh::LeanObject,
    mut v_t_1482_: *mut leanh::LeanObject,
    mut v_h_1483_: *mut leanh::LeanObject,
    mut v_sigwinch_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1485_: u8 = 0;
    let mut v_res_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1485_ = (leanh::lean_unbox(v_t_1482_) as u8);
    v_res_1486_ = l_Std_Async_Signal_sigwinch_elim(
        v_motive_1481_,
        v_t_boxed_1485_,
        v_h_1483_,
        v_sigwinch_1484_,
    );
    leanh::lean_dec(v_sigwinch_1484_);
    return v_res_1486_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim___redArg(
    mut v_sigio_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigio_1487_);
    return v_sigio_1487_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim___redArg___boxed(
    mut v_sigio_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1489_ = l_Std_Async_Signal_sigio_elim___redArg(v_sigio_1488_);
    leanh::lean_dec(v_sigio_1488_);
    return v_res_1489_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim(
    mut v_motive_1490_: *mut leanh::LeanObject,
    mut v_t_1491_: u8,
    mut v_h_1492_: *mut leanh::LeanObject,
    mut v_sigio_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigio_1493_);
    return v_sigio_1493_;
}
pub unsafe fn l_Std_Async_Signal_sigio_elim___boxed(
    mut v_motive_1494_: *mut leanh::LeanObject,
    mut v_t_1495_: *mut leanh::LeanObject,
    mut v_h_1496_: *mut leanh::LeanObject,
    mut v_sigio_1497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1498_: u8 = 0;
    let mut v_res_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1498_ = (leanh::lean_unbox(v_t_1495_) as u8);
    v_res_1499_ =
        l_Std_Async_Signal_sigio_elim(v_motive_1494_, v_t_boxed_1498_, v_h_1496_, v_sigio_1497_);
    leanh::lean_dec(v_sigio_1497_);
    return v_res_1499_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim___redArg(
    mut v_sigsys_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigsys_1500_);
    return v_sigsys_1500_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim___redArg___boxed(
    mut v_sigsys_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Std_Async_Signal_sigsys_elim___redArg(v_sigsys_1501_);
    leanh::lean_dec(v_sigsys_1501_);
    return v_res_1502_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim(
    mut v_motive_1503_: *mut leanh::LeanObject,
    mut v_t_1504_: u8,
    mut v_h_1505_: *mut leanh::LeanObject,
    mut v_sigsys_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_sigsys_1506_);
    return v_sigsys_1506_;
}
pub unsafe fn l_Std_Async_Signal_sigsys_elim___boxed(
    mut v_motive_1507_: *mut leanh::LeanObject,
    mut v_t_1508_: *mut leanh::LeanObject,
    mut v_h_1509_: *mut leanh::LeanObject,
    mut v_sigsys_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1511_: u8 = 0;
    let mut v_res_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1511_ = (leanh::lean_unbox(v_t_1508_) as u8);
    v_res_1512_ =
        l_Std_Async_Signal_sigsys_elim(v_motive_1507_, v_t_boxed_1511_, v_h_1509_, v_sigsys_1510_);
    leanh::lean_dec(v_sigsys_1510_);
    return v_res_1512_;
}
pub unsafe fn _init_l_Std_Async_instReprSignal_repr___closed__44() -> *mut leanh::LeanObject
{
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1579_ = leanh::lean_unsigned_to_nat(2);
    v___x_1580_ = lean_nat_to_int(v___x_1579_);
    return v___x_1580_;
}
pub unsafe fn _init_l_Std_Async_instReprSignal_repr___closed__45() -> *mut leanh::LeanObject
{
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = leanh::lean_unsigned_to_nat(1);
    v___x_1582_ = lean_nat_to_int(v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn l_Std_Async_instReprSignal_repr(
    mut v_x_1583_: u8,
    mut v_prec_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: u8 = 0;
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u8 = 0;
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1583_ {
                0 => {
                    v___x_1739_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1740_ = lean_nat_dec_le(v___x_1739_, v_prec_1584_);
                    if v___x_1740_ == 0 {
                        v___x_1741_ = leanh::lean_obj_once(
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
                        v___x_1742_ = leanh::lean_obj_once(
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
                    v___x_1743_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1744_ = lean_nat_dec_le(v___x_1743_, v_prec_1584_);
                    if v___x_1744_ == 0 {
                        v___x_1745_ = leanh::lean_obj_once(
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
                        v___x_1746_ = leanh::lean_obj_once(
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
                    v___x_1747_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1748_ = lean_nat_dec_le(v___x_1747_, v_prec_1584_);
                    if v___x_1748_ == 0 {
                        v___x_1749_ = leanh::lean_obj_once(
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
                        v___x_1750_ = leanh::lean_obj_once(
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
                    v___x_1751_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1752_ = lean_nat_dec_le(v___x_1751_, v_prec_1584_);
                    if v___x_1752_ == 0 {
                        v___x_1753_ = leanh::lean_obj_once(
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
                        v___x_1754_ = leanh::lean_obj_once(
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
                    v___x_1755_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1756_ = lean_nat_dec_le(v___x_1755_, v_prec_1584_);
                    if v___x_1756_ == 0 {
                        v___x_1757_ = leanh::lean_obj_once(
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
                        v___x_1758_ = leanh::lean_obj_once(
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
                    v___x_1759_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1760_ = lean_nat_dec_le(v___x_1759_, v_prec_1584_);
                    if v___x_1760_ == 0 {
                        v___x_1761_ = leanh::lean_obj_once(
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
                        v___x_1762_ = leanh::lean_obj_once(
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
                    v___x_1763_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1764_ = lean_nat_dec_le(v___x_1763_, v_prec_1584_);
                    if v___x_1764_ == 0 {
                        v___x_1765_ = leanh::lean_obj_once(
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
                        v___x_1766_ = leanh::lean_obj_once(
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
                    v___x_1767_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1768_ = lean_nat_dec_le(v___x_1767_, v_prec_1584_);
                    if v___x_1768_ == 0 {
                        v___x_1769_ = leanh::lean_obj_once(
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
                        v___x_1770_ = leanh::lean_obj_once(
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
                    v___x_1771_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1772_ = lean_nat_dec_le(v___x_1771_, v_prec_1584_);
                    if v___x_1772_ == 0 {
                        v___x_1773_ = leanh::lean_obj_once(
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
                        v___x_1774_ = leanh::lean_obj_once(
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
                    v___x_1775_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1776_ = lean_nat_dec_le(v___x_1775_, v_prec_1584_);
                    if v___x_1776_ == 0 {
                        v___x_1777_ = leanh::lean_obj_once(
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
                        v___x_1778_ = leanh::lean_obj_once(
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
                    v___x_1779_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1780_ = lean_nat_dec_le(v___x_1779_, v_prec_1584_);
                    if v___x_1780_ == 0 {
                        v___x_1781_ = leanh::lean_obj_once(
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
                        v___x_1782_ = leanh::lean_obj_once(
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
                    v___x_1783_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1784_ = lean_nat_dec_le(v___x_1783_, v_prec_1584_);
                    if v___x_1784_ == 0 {
                        v___x_1785_ = leanh::lean_obj_once(
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
                        v___x_1786_ = leanh::lean_obj_once(
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
                    v___x_1787_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1788_ = lean_nat_dec_le(v___x_1787_, v_prec_1584_);
                    if v___x_1788_ == 0 {
                        v___x_1789_ = leanh::lean_obj_once(
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
                        v___x_1790_ = leanh::lean_obj_once(
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
                    v___x_1791_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1792_ = lean_nat_dec_le(v___x_1791_, v_prec_1584_);
                    if v___x_1792_ == 0 {
                        v___x_1793_ = leanh::lean_obj_once(
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
                        v___x_1794_ = leanh::lean_obj_once(
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
                    v___x_1795_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1796_ = lean_nat_dec_le(v___x_1795_, v_prec_1584_);
                    if v___x_1796_ == 0 {
                        v___x_1797_ = leanh::lean_obj_once(
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
                        v___x_1798_ = leanh::lean_obj_once(
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
                    v___x_1799_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1800_ = lean_nat_dec_le(v___x_1799_, v_prec_1584_);
                    if v___x_1800_ == 0 {
                        v___x_1801_ = leanh::lean_obj_once(
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
                        v___x_1802_ = leanh::lean_obj_once(
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
                    v___x_1803_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1804_ = lean_nat_dec_le(v___x_1803_, v_prec_1584_);
                    if v___x_1804_ == 0 {
                        v___x_1805_ = leanh::lean_obj_once(
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
                        v___x_1806_ = leanh::lean_obj_once(
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
                    v___x_1807_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1808_ = lean_nat_dec_le(v___x_1807_, v_prec_1584_);
                    if v___x_1808_ == 0 {
                        v___x_1809_ = leanh::lean_obj_once(
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
                        v___x_1810_ = leanh::lean_obj_once(
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
                    v___x_1811_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1812_ = lean_nat_dec_le(v___x_1811_, v_prec_1584_);
                    if v___x_1812_ == 0 {
                        v___x_1813_ = leanh::lean_obj_once(
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
                        v___x_1814_ = leanh::lean_obj_once(
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
                    v___x_1815_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1816_ = lean_nat_dec_le(v___x_1815_, v_prec_1584_);
                    if v___x_1816_ == 0 {
                        v___x_1817_ = leanh::lean_obj_once(
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
                        v___x_1818_ = leanh::lean_obj_once(
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
                    v___x_1819_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1820_ = lean_nat_dec_le(v___x_1819_, v_prec_1584_);
                    if v___x_1820_ == 0 {
                        v___x_1821_ = leanh::lean_obj_once(
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
                        v___x_1822_ = leanh::lean_obj_once(
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
                    v___x_1823_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1824_ = lean_nat_dec_le(v___x_1823_, v_prec_1584_);
                    if v___x_1824_ == 0 {
                        v___x_1825_ = leanh::lean_obj_once(
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
                        v___x_1826_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_1586_);
                v___x_1588_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1588_, 0, v___y_1586_);
                leanh::lean_ctor_set(v___x_1588_, 1, v___x_1587_);
                v___x_1589_ = 0;
                v___x_1590_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1590_, 0, v___x_1588_);
                leanh::lean_ctor_set_uint8(
                    v___x_1590_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1589_,
                );
                v___x_1591_ = l_Repr_addAppParen(v___x_1590_, v_prec_1584_);
                return v___x_1591_;
            }
            2 => {
                v___x_1594_ = l_Std_Async_instReprSignal_repr___closed__3;
                leanh::lean_inc(v___y_1593_);
                v___x_1595_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1595_, 0, v___y_1593_);
                leanh::lean_ctor_set(v___x_1595_, 1, v___x_1594_);
                v___x_1596_ = 0;
                v___x_1597_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1597_, 0, v___x_1595_);
                leanh::lean_ctor_set_uint8(
                    v___x_1597_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1596_,
                );
                v___x_1598_ = l_Repr_addAppParen(v___x_1597_, v_prec_1584_);
                return v___x_1598_;
            }
            3 => {
                v___x_1601_ = l_Std_Async_instReprSignal_repr___closed__5;
                leanh::lean_inc(v___y_1600_);
                v___x_1602_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1602_, 0, v___y_1600_);
                leanh::lean_ctor_set(v___x_1602_, 1, v___x_1601_);
                v___x_1603_ = 0;
                v___x_1604_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1604_, 0, v___x_1602_);
                leanh::lean_ctor_set_uint8(
                    v___x_1604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1603_,
                );
                v___x_1605_ = l_Repr_addAppParen(v___x_1604_, v_prec_1584_);
                return v___x_1605_;
            }
            4 => {
                v___x_1608_ = l_Std_Async_instReprSignal_repr___closed__7;
                leanh::lean_inc(v___y_1607_);
                v___x_1609_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1609_, 0, v___y_1607_);
                leanh::lean_ctor_set(v___x_1609_, 1, v___x_1608_);
                v___x_1610_ = 0;
                v___x_1611_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1611_, 0, v___x_1609_);
                leanh::lean_ctor_set_uint8(
                    v___x_1611_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1610_,
                );
                v___x_1612_ = l_Repr_addAppParen(v___x_1611_, v_prec_1584_);
                return v___x_1612_;
            }
            5 => {
                v___x_1615_ = l_Std_Async_instReprSignal_repr___closed__9;
                leanh::lean_inc(v___y_1614_);
                v___x_1616_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1616_, 0, v___y_1614_);
                leanh::lean_ctor_set(v___x_1616_, 1, v___x_1615_);
                v___x_1617_ = 0;
                v___x_1618_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                leanh::lean_ctor_set_uint8(
                    v___x_1618_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1617_,
                );
                v___x_1619_ = l_Repr_addAppParen(v___x_1618_, v_prec_1584_);
                return v___x_1619_;
            }
            6 => {
                v___x_1622_ = l_Std_Async_instReprSignal_repr___closed__11;
                leanh::lean_inc(v___y_1621_);
                v___x_1623_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1623_, 0, v___y_1621_);
                leanh::lean_ctor_set(v___x_1623_, 1, v___x_1622_);
                v___x_1624_ = 0;
                v___x_1625_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1625_, 0, v___x_1623_);
                leanh::lean_ctor_set_uint8(
                    v___x_1625_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1624_,
                );
                v___x_1626_ = l_Repr_addAppParen(v___x_1625_, v_prec_1584_);
                return v___x_1626_;
            }
            7 => {
                v___x_1629_ = l_Std_Async_instReprSignal_repr___closed__13;
                leanh::lean_inc(v___y_1628_);
                v___x_1630_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1630_, 0, v___y_1628_);
                leanh::lean_ctor_set(v___x_1630_, 1, v___x_1629_);
                v___x_1631_ = 0;
                v___x_1632_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1632_, 0, v___x_1630_);
                leanh::lean_ctor_set_uint8(
                    v___x_1632_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1631_,
                );
                v___x_1633_ = l_Repr_addAppParen(v___x_1632_, v_prec_1584_);
                return v___x_1633_;
            }
            8 => {
                v___x_1636_ = l_Std_Async_instReprSignal_repr___closed__15;
                leanh::lean_inc(v___y_1635_);
                v___x_1637_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1637_, 0, v___y_1635_);
                leanh::lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                v___x_1638_ = 0;
                v___x_1639_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1639_, 0, v___x_1637_);
                leanh::lean_ctor_set_uint8(
                    v___x_1639_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1638_,
                );
                v___x_1640_ = l_Repr_addAppParen(v___x_1639_, v_prec_1584_);
                return v___x_1640_;
            }
            9 => {
                v___x_1643_ = l_Std_Async_instReprSignal_repr___closed__17;
                leanh::lean_inc(v___y_1642_);
                v___x_1644_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1644_, 0, v___y_1642_);
                leanh::lean_ctor_set(v___x_1644_, 1, v___x_1643_);
                v___x_1645_ = 0;
                v___x_1646_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1646_, 0, v___x_1644_);
                leanh::lean_ctor_set_uint8(
                    v___x_1646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1645_,
                );
                v___x_1647_ = l_Repr_addAppParen(v___x_1646_, v_prec_1584_);
                return v___x_1647_;
            }
            10 => {
                v___x_1650_ = l_Std_Async_instReprSignal_repr___closed__19;
                leanh::lean_inc(v___y_1649_);
                v___x_1651_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1651_, 0, v___y_1649_);
                leanh::lean_ctor_set(v___x_1651_, 1, v___x_1650_);
                v___x_1652_ = 0;
                v___x_1653_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1653_, 0, v___x_1651_);
                leanh::lean_ctor_set_uint8(
                    v___x_1653_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1652_,
                );
                v___x_1654_ = l_Repr_addAppParen(v___x_1653_, v_prec_1584_);
                return v___x_1654_;
            }
            11 => {
                v___x_1657_ = l_Std_Async_instReprSignal_repr___closed__21;
                leanh::lean_inc(v___y_1656_);
                v___x_1658_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1658_, 0, v___y_1656_);
                leanh::lean_ctor_set(v___x_1658_, 1, v___x_1657_);
                v___x_1659_ = 0;
                v___x_1660_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1660_, 0, v___x_1658_);
                leanh::lean_ctor_set_uint8(
                    v___x_1660_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1659_,
                );
                v___x_1661_ = l_Repr_addAppParen(v___x_1660_, v_prec_1584_);
                return v___x_1661_;
            }
            12 => {
                v___x_1664_ = l_Std_Async_instReprSignal_repr___closed__23;
                leanh::lean_inc(v___y_1663_);
                v___x_1665_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1665_, 0, v___y_1663_);
                leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v___x_1666_ = 0;
                v___x_1667_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1667_, 0, v___x_1665_);
                leanh::lean_ctor_set_uint8(
                    v___x_1667_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1666_,
                );
                v___x_1668_ = l_Repr_addAppParen(v___x_1667_, v_prec_1584_);
                return v___x_1668_;
            }
            13 => {
                v___x_1671_ = l_Std_Async_instReprSignal_repr___closed__25;
                leanh::lean_inc(v___y_1670_);
                v___x_1672_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1672_, 0, v___y_1670_);
                leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                v___x_1673_ = 0;
                v___x_1674_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1674_, 0, v___x_1672_);
                leanh::lean_ctor_set_uint8(
                    v___x_1674_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1673_,
                );
                v___x_1675_ = l_Repr_addAppParen(v___x_1674_, v_prec_1584_);
                return v___x_1675_;
            }
            14 => {
                v___x_1678_ = l_Std_Async_instReprSignal_repr___closed__27;
                leanh::lean_inc(v___y_1677_);
                v___x_1679_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1679_, 0, v___y_1677_);
                leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
                v___x_1680_ = 0;
                v___x_1681_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1681_, 0, v___x_1679_);
                leanh::lean_ctor_set_uint8(
                    v___x_1681_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1680_,
                );
                v___x_1682_ = l_Repr_addAppParen(v___x_1681_, v_prec_1584_);
                return v___x_1682_;
            }
            15 => {
                v___x_1685_ = l_Std_Async_instReprSignal_repr___closed__29;
                leanh::lean_inc(v___y_1684_);
                v___x_1686_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1686_, 0, v___y_1684_);
                leanh::lean_ctor_set(v___x_1686_, 1, v___x_1685_);
                v___x_1687_ = 0;
                v___x_1688_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1688_, 0, v___x_1686_);
                leanh::lean_ctor_set_uint8(
                    v___x_1688_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1687_,
                );
                v___x_1689_ = l_Repr_addAppParen(v___x_1688_, v_prec_1584_);
                return v___x_1689_;
            }
            16 => {
                v___x_1692_ = l_Std_Async_instReprSignal_repr___closed__31;
                leanh::lean_inc(v___y_1691_);
                v___x_1693_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1693_, 0, v___y_1691_);
                leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                v___x_1694_ = 0;
                v___x_1695_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1695_, 0, v___x_1693_);
                leanh::lean_ctor_set_uint8(
                    v___x_1695_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1694_,
                );
                v___x_1696_ = l_Repr_addAppParen(v___x_1695_, v_prec_1584_);
                return v___x_1696_;
            }
            17 => {
                v___x_1699_ = l_Std_Async_instReprSignal_repr___closed__33;
                leanh::lean_inc(v___y_1698_);
                v___x_1700_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1700_, 0, v___y_1698_);
                leanh::lean_ctor_set(v___x_1700_, 1, v___x_1699_);
                v___x_1701_ = 0;
                v___x_1702_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1702_, 0, v___x_1700_);
                leanh::lean_ctor_set_uint8(
                    v___x_1702_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1701_,
                );
                v___x_1703_ = l_Repr_addAppParen(v___x_1702_, v_prec_1584_);
                return v___x_1703_;
            }
            18 => {
                v___x_1706_ = l_Std_Async_instReprSignal_repr___closed__35;
                leanh::lean_inc(v___y_1705_);
                v___x_1707_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1707_, 0, v___y_1705_);
                leanh::lean_ctor_set(v___x_1707_, 1, v___x_1706_);
                v___x_1708_ = 0;
                v___x_1709_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1709_, 0, v___x_1707_);
                leanh::lean_ctor_set_uint8(
                    v___x_1709_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1708_,
                );
                v___x_1710_ = l_Repr_addAppParen(v___x_1709_, v_prec_1584_);
                return v___x_1710_;
            }
            19 => {
                v___x_1713_ = l_Std_Async_instReprSignal_repr___closed__37;
                leanh::lean_inc(v___y_1712_);
                v___x_1714_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1714_, 0, v___y_1712_);
                leanh::lean_ctor_set(v___x_1714_, 1, v___x_1713_);
                v___x_1715_ = 0;
                v___x_1716_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1716_, 0, v___x_1714_);
                leanh::lean_ctor_set_uint8(
                    v___x_1716_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1715_,
                );
                v___x_1717_ = l_Repr_addAppParen(v___x_1716_, v_prec_1584_);
                return v___x_1717_;
            }
            20 => {
                v___x_1720_ = l_Std_Async_instReprSignal_repr___closed__39;
                leanh::lean_inc(v___y_1719_);
                v___x_1721_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1721_, 0, v___y_1719_);
                leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                v___x_1722_ = 0;
                v___x_1723_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1723_, 0, v___x_1721_);
                leanh::lean_ctor_set_uint8(
                    v___x_1723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1722_,
                );
                v___x_1724_ = l_Repr_addAppParen(v___x_1723_, v_prec_1584_);
                return v___x_1724_;
            }
            21 => {
                v___x_1727_ = l_Std_Async_instReprSignal_repr___closed__41;
                leanh::lean_inc(v___y_1726_);
                v___x_1728_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1728_, 0, v___y_1726_);
                leanh::lean_ctor_set(v___x_1728_, 1, v___x_1727_);
                v___x_1729_ = 0;
                v___x_1730_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1730_, 0, v___x_1728_);
                leanh::lean_ctor_set_uint8(
                    v___x_1730_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1729_,
                );
                v___x_1731_ = l_Repr_addAppParen(v___x_1730_, v_prec_1584_);
                return v___x_1731_;
            }
            22 => {
                v___x_1734_ = l_Std_Async_instReprSignal_repr___closed__43;
                leanh::lean_inc(v___y_1733_);
                v___x_1735_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1735_, 0, v___y_1733_);
                leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
                v___x_1736_ = 0;
                v___x_1737_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1737_, 0, v___x_1735_);
                leanh::lean_ctor_set_uint8(
                    v___x_1737_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_1827_: *mut leanh::LeanObject,
    mut v_prec_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1241__boxed_1829_: u8 = 0;
    let mut v_res_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1241__boxed_1829_ = (leanh::lean_unbox(v_x_1827_) as u8);
    v_res_1830_ = l_Std_Async_instReprSignal_repr(v_x_1241__boxed_1829_, v_prec_1828_);
    leanh::lean_dec(v_prec_1828_);
    return v_res_1830_;
}
pub unsafe fn l_Std_Async_Signal_ofNat(mut v_n_1833_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    v___x_1834_ = leanh::lean_unsigned_to_nat(10);
    v___x_1835_ = lean_nat_dec_le(v_n_1833_, v___x_1834_);
    if v___x_1835_ == 0 {
        let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: u8 = 0;
        v___x_1836_ = leanh::lean_unsigned_to_nat(15);
        v___x_1837_ = lean_nat_dec_le(v_n_1833_, v___x_1836_);
        if v___x_1837_ == 0 {
            let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1839_: u8 = 0;
            v___x_1838_ = leanh::lean_unsigned_to_nat(18);
            v___x_1839_ = lean_nat_dec_le(v_n_1833_, v___x_1838_);
            if v___x_1839_ == 0 {
                let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1841_: u8 = 0;
                v___x_1840_ = leanh::lean_unsigned_to_nat(19);
                v___x_1841_ = lean_nat_dec_le(v_n_1833_, v___x_1840_);
                if v___x_1841_ == 0 {
                    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1843_: u8 = 0;
                    v___x_1842_ = leanh::lean_unsigned_to_nat(20);
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
                let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1848_: u8 = 0;
                v___x_1847_ = leanh::lean_unsigned_to_nat(16);
                v___x_1848_ = lean_nat_dec_le(v_n_1833_, v___x_1847_);
                if v___x_1848_ == 0 {
                    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1850_: u8 = 0;
                    v___x_1849_ = leanh::lean_unsigned_to_nat(17);
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
            let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1855_: u8 = 0;
            v___x_1854_ = leanh::lean_unsigned_to_nat(12);
            v___x_1855_ = lean_nat_dec_le(v_n_1833_, v___x_1854_);
            if v___x_1855_ == 0 {
                let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1857_: u8 = 0;
                v___x_1856_ = leanh::lean_unsigned_to_nat(13);
                v___x_1857_ = lean_nat_dec_le(v_n_1833_, v___x_1856_);
                if v___x_1857_ == 0 {
                    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1859_: u8 = 0;
                    v___x_1858_ = leanh::lean_unsigned_to_nat(14);
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
                let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1864_: u8 = 0;
                v___x_1863_ = leanh::lean_unsigned_to_nat(11);
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
        let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: u8 = 0;
        v___x_1867_ = leanh::lean_unsigned_to_nat(4);
        v___x_1868_ = lean_nat_dec_le(v_n_1833_, v___x_1867_);
        if v___x_1868_ == 0 {
            let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1870_: u8 = 0;
            v___x_1869_ = leanh::lean_unsigned_to_nat(7);
            v___x_1870_ = lean_nat_dec_le(v_n_1833_, v___x_1869_);
            if v___x_1870_ == 0 {
                let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1872_: u8 = 0;
                v___x_1871_ = leanh::lean_unsigned_to_nat(8);
                v___x_1872_ = lean_nat_dec_le(v_n_1833_, v___x_1871_);
                if v___x_1872_ == 0 {
                    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1874_: u8 = 0;
                    v___x_1873_ = leanh::lean_unsigned_to_nat(9);
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
                let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1879_: u8 = 0;
                v___x_1878_ = leanh::lean_unsigned_to_nat(5);
                v___x_1879_ = lean_nat_dec_le(v_n_1833_, v___x_1878_);
                if v___x_1879_ == 0 {
                    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1881_: u8 = 0;
                    v___x_1880_ = leanh::lean_unsigned_to_nat(6);
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
            let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1886_: u8 = 0;
            v___x_1885_ = leanh::lean_unsigned_to_nat(1);
            v___x_1886_ = lean_nat_dec_le(v_n_1833_, v___x_1885_);
            if v___x_1886_ == 0 {
                let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1888_: u8 = 0;
                v___x_1887_ = leanh::lean_unsigned_to_nat(2);
                v___x_1888_ = lean_nat_dec_le(v_n_1833_, v___x_1887_);
                if v___x_1888_ == 0 {
                    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1890_: u8 = 0;
                    v___x_1889_ = leanh::lean_unsigned_to_nat(3);
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
                let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1895_: u8 = 0;
                v___x_1894_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_n_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1899_: u8 = 0;
    let mut v_r_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1899_ = l_Std_Async_Signal_ofNat(v_n_1898_);
    leanh::lean_dec(v_n_1898_);
    v_r_1900_ = leanh::lean_box((v_res_1899_) as usize);
    return v_r_1900_;
}
pub unsafe fn l_Std_Async_instDecidableEqSignal(mut v_x_1901_: u8, mut v_y_1902_: u8) -> u8 {
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: u8 = 0;
    v___x_1903_ = l_Std_Async_Signal_ctorIdx(v_x_1901_);
    v___x_1904_ = l_Std_Async_Signal_ctorIdx(v_y_1902_);
    v___x_1905_ = lean_nat_dec_eq(v___x_1903_, v___x_1904_);
    leanh::lean_dec(v___x_1904_);
    leanh::lean_dec(v___x_1903_);
    return v___x_1905_;
}
pub unsafe fn l_Std_Async_instDecidableEqSignal___boxed(
    mut v_x_1906_: *mut leanh::LeanObject,
    mut v_y_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13__boxed_1908_: u8 = 0;
    let mut v_y_14__boxed_1909_: u8 = 0;
    let mut v_res_1910_: u8 = 0;
    let mut v_r_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_1908_ = (leanh::lean_unbox(v_x_1906_) as u8);
    v_y_14__boxed_1909_ = (leanh::lean_unbox(v_y_1907_) as u8);
    v_res_1910_ = l_Std_Async_instDecidableEqSignal(v_x_13__boxed_1908_, v_y_14__boxed_1909_);
    v_r_1911_ = leanh::lean_box((v_res_1910_) as usize);
    return v_r_1911_;
}
pub unsafe fn l_Std_Async_instBEqSignal_beq(mut v_x_1912_: u8, mut v_y_1913_: u8) -> u8 {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: u8 = 0;
    v___x_1914_ = l_Std_Async_Signal_ctorIdx(v_x_1912_);
    v___x_1915_ = l_Std_Async_Signal_ctorIdx(v_y_1913_);
    v___x_1916_ = lean_nat_dec_eq(v___x_1914_, v___x_1915_);
    leanh::lean_dec(v___x_1915_);
    leanh::lean_dec(v___x_1914_);
    return v___x_1916_;
}
pub unsafe fn l_Std_Async_instBEqSignal_beq___boxed(
    mut v_x_1917_: *mut leanh::LeanObject,
    mut v_y_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_1919_: u8 = 0;
    let mut v_y_18__boxed_1920_: u8 = 0;
    let mut v_res_1921_: u8 = 0;
    let mut v_r_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1919_ = (leanh::lean_unbox(v_x_1917_) as u8);
    v_y_18__boxed_1920_ = (leanh::lean_unbox(v_y_1918_) as u8);
    v_res_1921_ = l_Std_Async_instBEqSignal_beq(v_x_17__boxed_1919_, v_y_18__boxed_1920_);
    v_r_1922_ = leanh::lean_box((v_res_1921_) as usize);
    return v_r_1922_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__0() -> u32 {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u32 = 0;
    v___x_1925_ = leanh::lean_unsigned_to_nat(1);
    v___x_1926_ = lean_int32_of_nat(v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__1() -> u32 {
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: u32 = 0;
    v___x_1927_ = leanh::lean_unsigned_to_nat(2);
    v___x_1928_ = lean_int32_of_nat(v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__2() -> u32 {
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u32 = 0;
    v___x_1929_ = leanh::lean_unsigned_to_nat(3);
    v___x_1930_ = lean_int32_of_nat(v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__3() -> u32 {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u32 = 0;
    v___x_1931_ = leanh::lean_unsigned_to_nat(5);
    v___x_1932_ = lean_int32_of_nat(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__4() -> u32 {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u32 = 0;
    v___x_1933_ = leanh::lean_unsigned_to_nat(6);
    v___x_1934_ = lean_int32_of_nat(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__5() -> u32 {
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: u32 = 0;
    v___x_1935_ = leanh::lean_unsigned_to_nat(10);
    v___x_1936_ = lean_int32_of_nat(v___x_1935_);
    return v___x_1936_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__6() -> u32 {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u32 = 0;
    v___x_1937_ = leanh::lean_unsigned_to_nat(12);
    v___x_1938_ = lean_int32_of_nat(v___x_1937_);
    return v___x_1938_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__7() -> u32 {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u32 = 0;
    v___x_1939_ = leanh::lean_unsigned_to_nat(14);
    v___x_1940_ = lean_int32_of_nat(v___x_1939_);
    return v___x_1940_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__8() -> u32 {
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u32 = 0;
    v___x_1941_ = leanh::lean_unsigned_to_nat(15);
    v___x_1942_ = lean_int32_of_nat(v___x_1941_);
    return v___x_1942_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__9() -> u32 {
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u32 = 0;
    v___x_1943_ = leanh::lean_unsigned_to_nat(17);
    v___x_1944_ = lean_int32_of_nat(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__10() -> u32 {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u32 = 0;
    v___x_1945_ = leanh::lean_unsigned_to_nat(18);
    v___x_1946_ = lean_int32_of_nat(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__11() -> u32 {
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u32 = 0;
    v___x_1947_ = leanh::lean_unsigned_to_nat(20);
    v___x_1948_ = lean_int32_of_nat(v___x_1947_);
    return v___x_1948_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__12() -> u32 {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u32 = 0;
    v___x_1949_ = leanh::lean_unsigned_to_nat(21);
    v___x_1950_ = lean_int32_of_nat(v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__13() -> u32 {
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u32 = 0;
    v___x_1951_ = leanh::lean_unsigned_to_nat(22);
    v___x_1952_ = lean_int32_of_nat(v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__14() -> u32 {
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u32 = 0;
    v___x_1953_ = leanh::lean_unsigned_to_nat(23);
    v___x_1954_ = lean_int32_of_nat(v___x_1953_);
    return v___x_1954_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__15() -> u32 {
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u32 = 0;
    v___x_1955_ = leanh::lean_unsigned_to_nat(24);
    v___x_1956_ = lean_int32_of_nat(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__16() -> u32 {
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u32 = 0;
    v___x_1957_ = leanh::lean_unsigned_to_nat(25);
    v___x_1958_ = lean_int32_of_nat(v___x_1957_);
    return v___x_1958_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__17() -> u32 {
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u32 = 0;
    v___x_1959_ = leanh::lean_unsigned_to_nat(26);
    v___x_1960_ = lean_int32_of_nat(v___x_1959_);
    return v___x_1960_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__18() -> u32 {
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u32 = 0;
    v___x_1961_ = leanh::lean_unsigned_to_nat(27);
    v___x_1962_ = lean_int32_of_nat(v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__19() -> u32 {
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u32 = 0;
    v___x_1963_ = leanh::lean_unsigned_to_nat(28);
    v___x_1964_ = lean_int32_of_nat(v___x_1963_);
    return v___x_1964_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__20() -> u32 {
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u32 = 0;
    v___x_1965_ = leanh::lean_unsigned_to_nat(29);
    v___x_1966_ = lean_int32_of_nat(v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn _init_l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32___closed__21() -> u32 {
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u32 = 0;
    v___x_1967_ = leanh::lean_unsigned_to_nat(31);
    v___x_1968_ = lean_int32_of_nat(v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(mut v_x_1969_: u8) -> u32 {
    match v_x_1969_ {
        0 => {
            let mut v___x_1970_: u32 = 0;
            v___x_1970_ = leanh::lean_uint32_once(
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
            v___x_1971_ = leanh::lean_uint32_once(
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
            v___x_1972_ = leanh::lean_uint32_once(
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
            v___x_1973_ = leanh::lean_uint32_once(
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
            v___x_1974_ = leanh::lean_uint32_once(
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
            v___x_1975_ = leanh::lean_uint32_once(
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
            v___x_1976_ = leanh::lean_uint32_once(
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
            v___x_1977_ = leanh::lean_uint32_once(
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
            v___x_1978_ = leanh::lean_uint32_once(
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
            v___x_1979_ = leanh::lean_uint32_once(
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
            v___x_1980_ = leanh::lean_uint32_once(
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
            v___x_1981_ = leanh::lean_uint32_once(
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
            v___x_1982_ = leanh::lean_uint32_once(
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
            v___x_1983_ = leanh::lean_uint32_once(
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
            v___x_1984_ = leanh::lean_uint32_once(
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
            v___x_1985_ = leanh::lean_uint32_once(
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
            v___x_1986_ = leanh::lean_uint32_once(
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
            v___x_1987_ = leanh::lean_uint32_once(
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
            v___x_1988_ = leanh::lean_uint32_once(
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
            v___x_1989_ = leanh::lean_uint32_once(
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
            v___x_1990_ = leanh::lean_uint32_once(
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
            v___x_1991_ = leanh::lean_uint32_once(
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
    mut v_x_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_356__boxed_1993_: u8 = 0;
    let mut v_res_1994_: u32 = 0;
    let mut v_r_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_356__boxed_1993_ = (leanh::lean_unbox(v_x_1992_) as u8);
    v_res_1994_ = l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_x_356__boxed_1993_);
    v_r_1995_ = leanh::lean_box_uint32(v_res_1994_);
    return v_r_1995_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_mk(
    mut v_signum_1996_: u8,
    mut v_repeating_1997_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1999_: u32 = 0;
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v_a_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1999_ =
                    l___private_Std_Async_Signal_0__Std_Async_Signal_toInt32(v_signum_1996_);
                v___x_2000_ = lean_uv_signal_mk(v___x_1999_, v_repeating_1997_);
                if leanh::lean_obj_tag(v___x_2000_) == 0 {
                    v_a_2001_ = leanh::lean_ctor_get(v___x_2000_, 0);
                    v_isSharedCheck_2008_ = (!leanh::lean_is_exclusive(v___x_2000_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_2003_ = v___x_2000_;
                        v_isShared_2004_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2001_);
                        leanh::lean_dec(v___x_2000_);
                        v___x_2003_ = leanh::lean_box(0);
                        v_isShared_2004_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2009_ = leanh::lean_ctor_get(v___x_2000_, 0);
                    v_isSharedCheck_2016_ = (!leanh::lean_is_exclusive(v___x_2000_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2011_ = v___x_2000_;
                        v_isShared_2012_ = v_isSharedCheck_2016_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2009_);
                        leanh::lean_dec(v___x_2000_);
                        v___x_2011_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
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
                    v_reuseFailAlloc_2015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
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
    mut v_signum_2017_: *mut leanh::LeanObject,
    mut v_repeating_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_signum_boxed_2020_: u8 = 0;
    let mut v_repeating_boxed_2021_: u8 = 0;
    let mut v_res_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_signum_boxed_2020_ = (leanh::lean_unbox(v_signum_2017_) as u8);
    v_repeating_boxed_2021_ = (leanh::lean_unbox(v_repeating_2018_) as u8);
    v_res_2022_ = l_Std_Async_Signal_Waiter_mk(v_signum_boxed_2020_, v_repeating_boxed_2021_);
    return v_res_2022_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_wait___lam__0(
    mut v___x_2023_: *mut leanh::LeanObject,
    mut v_x_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2024_) == 0 {
                    v___x_2025_ = lean_mk_io_user_error(v___x_2023_);
                    v___x_2026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2026_, 0, v___x_2025_);
                    return v___x_2026_;
                } else {
                    leanh::lean_dec_ref(v___x_2023_);
                    v_val_2027_ = leanh::lean_ctor_get(v_x_2024_, 0);
                    v_isSharedCheck_2034_ = (!leanh::lean_is_exclusive(v_x_2024_)) as u8;
                    if v_isSharedCheck_2034_ == 0 {
                        v___x_2029_ = v_x_2024_;
                        v_isShared_2030_ = v_isSharedCheck_2034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2027_);
                        leanh::lean_dec(v_x_2024_);
                        v___x_2029_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2033_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_val_2027_);
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
    mut v_s_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v___f_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: u8 = 0;
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2053_: u8 = 0;
    let mut v_a_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2040_ = lean_uv_signal_next(v_s_2038_);
                if leanh::lean_obj_tag(v___x_2040_) == 0 {
                    v_a_2041_ = leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2053_ = (!leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2053_ == 0 {
                        v___x_2043_ = v___x_2040_;
                        v_isShared_2044_ = v_isSharedCheck_2053_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2041_);
                        leanh::lean_dec(v___x_2040_);
                        v___x_2043_ = leanh::lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2053_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2054_ = leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2061_ = (!leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2061_ == 0 {
                        v___x_2056_ = v___x_2040_;
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2054_);
                        leanh::lean_dec(v___x_2040_);
                        v___x_2056_ = leanh::lean_box(0);
                        v_isShared_2057_ = v_isSharedCheck_2061_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_2045_ = l_Std_Async_Signal_Waiter_wait___closed__1;
                v___x_2046_ = lean_io_promise_result_opt(v_a_2041_);
                leanh::lean_dec(v_a_2041_);
                v___x_2047_ = leanh::lean_unsigned_to_nat(0);
                v___x_2048_ = 1;
                v___x_2049_ = lean_task_map(v___f_2045_, v___x_2046_, v___x_2047_, v___x_2048_);
                if v_isShared_2044_ == 0 {
                    leanh::lean_ctor_set(v___x_2043_, 0, v___x_2049_);
                    v___x_2051_ = v___x_2043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
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
                    v_reuseFailAlloc_2060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
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
    mut v_s_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Std_Async_Signal_Waiter_wait(v_s_2062_);
    leanh::lean_dec(v_s_2062_);
    return v_res_2064_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_stop(
    mut v_s_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = lean_uv_signal_stop(v_s_2065_);
    return v___x_2067_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_stop___boxed(
    mut v_s_2068_: *mut leanh::LeanObject,
    mut v_a_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Std_Async_Signal_Waiter_stop(v_s_2068_);
    leanh::lean_dec(v_s_2068_);
    return v_res_2070_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(
    mut v_w_2073_: *mut leanh::LeanObject,
    mut v_lose_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_finished_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_2076_ = leanh::lean_ctor_get(v_w_2073_, 0);
                v_promise_2077_ = leanh::lean_ctor_get(v_w_2073_, 1);
                v___x_2078_ = lean_st_ref_take(v_finished_2076_);
                v___x_2088_ = (leanh::lean_unbox(v___x_2078_) as u8);
                leanh::lean_dec(v___x_2078_);
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
                v___x_2082_ = leanh::lean_box((v___x_2081_) as usize);
                v___x_2083_ = lean_st_ref_set(v_finished_2076_, v___x_2082_);
                if v___y_2080_ == 0 {
                    v___x_2084_ =
                        leanh::lean_apply_1(v_lose_2074_, leanh::lean_box(0));
                    return v___x_2084_;
                } else {
                    leanh::lean_dec_ref(v_lose_2074_);
                    v___x_2085_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___closed__0;
                    v___x_2086_ = lean_io_promise_resolve(v___x_2085_, v_promise_2077_);
                    v___x_2087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2087_, 0, v___x_2086_);
                    return v___x_2087_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0___boxed(
    mut v_w_2091_: *mut leanh::LeanObject,
    mut v_lose_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2094_ = l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(
        v_w_2091_,
        v_lose_2092_,
    );
    leanh::lean_dec_ref(v_w_2091_);
    return v_res_2094_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__0(
    mut v_s_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2100_ = lean_uv_signal_cancel(v_s_2095_);
                if leanh::lean_obj_tag(v___x_2100_) == 0 {
                    v_a_2101_ = leanh::lean_ctor_get(v___x_2100_, 0);
                    v_isSharedCheck_2108_ = (!leanh::lean_is_exclusive(v___x_2100_)) as u8;
                    if v_isSharedCheck_2108_ == 0 {
                        v___x_2103_ = v___x_2100_;
                        v_isShared_2104_ = v_isSharedCheck_2108_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2101_);
                        leanh::lean_dec(v___x_2100_);
                        v___x_2103_ = leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2108_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2109_ = leanh::lean_ctor_get(v___x_2100_, 0);
                    v_isSharedCheck_2116_ = (!leanh::lean_is_exclusive(v___x_2100_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2111_ = v___x_2100_;
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2109_);
                        leanh::lean_dec(v___x_2100_);
                        v___x_2111_ = leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2099_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2099_, 0, v_val_2098_);
                return v___x_2099_;
            }
            2 => {
                if v_isShared_2104_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2103_, 1);
                    v___x_2106_ = v___x_2103_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
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
                    leanh::lean_ctor_set_tag(v___x_2111_, 0);
                    v___x_2114_ = v___x_2111_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
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
    mut v_s_2117_: *mut leanh::LeanObject,
    mut v___y_2118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2119_ = l_Std_Async_Signal_Waiter_selector___lam__0(v_s_2117_);
    leanh::lean_dec(v_s_2117_);
    return v_res_2119_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__1(
    mut v_x_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2124_) == 0 {
                    v_a_2126_ = leanh::lean_ctor_get(v_x_2124_, 0);
                    v_isSharedCheck_2134_ = (!leanh::lean_is_exclusive(v_x_2124_)) as u8;
                    if v_isSharedCheck_2134_ == 0 {
                        v___x_2128_ = v_x_2124_;
                        v_isShared_2129_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2126_);
                        leanh::lean_dec(v_x_2124_);
                        v___x_2128_ = leanh::lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_2124_, 1);
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
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2126_);
                    v___x_2131_ = v_reuseFailAlloc_2133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2132_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                return v___x_2132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__1___boxed(
    mut v_x_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Std_Async_Signal_Waiter_selector___lam__1(v_x_2136_);
    return v_res_2138_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__2(
    mut v___f_2145_: *mut leanh::LeanObject,
    mut v_s_2146_: *mut leanh::LeanObject,
    mut v_x_2147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_a_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_val_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2147_) == 0 {
                    leanh::lean_dec_ref(v___f_2145_);
                    v_a_2149_ = leanh::lean_ctor_get(v_x_2147_, 0);
                    v_isSharedCheck_2157_ = (!leanh::lean_is_exclusive(v_x_2147_)) as u8;
                    if v_isSharedCheck_2157_ == 0 {
                        v___x_2151_ = v_x_2147_;
                        v_isShared_2152_ = v_isSharedCheck_2157_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2149_);
                        leanh::lean_dec(v_x_2147_);
                        v___x_2151_ = leanh::lean_box(0);
                        v_isShared_2152_ = v_isSharedCheck_2157_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2158_ = leanh::lean_ctor_get(v_x_2147_, 0);
                    v_isSharedCheck_2179_ = (!leanh::lean_is_exclusive(v_x_2147_)) as u8;
                    if v_isSharedCheck_2179_ == 0 {
                        v___x_2160_ = v_x_2147_;
                        v_isShared_2161_ = v_isSharedCheck_2179_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2158_);
                        leanh::lean_dec(v_x_2147_);
                        v___x_2160_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2149_);
                    v___x_2154_ = v_reuseFailAlloc_2156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                return v___x_2155_;
            }
            3 => {
                v___x_2168_ = (leanh::lean_unbox(v_a_2158_) as u8);
                if v___x_2168_ == 0 {
                    v___x_2169_ = lean_uv_signal_cancel(v_s_2146_);
                    if leanh::lean_obj_tag(v___x_2169_) == 0 {
                        v_a_2170_ = leanh::lean_ctor_get(v___x_2169_, 0);
                        leanh::lean_inc(v_a_2170_);
                        leanh::lean_dec_ref_known(v___x_2169_, 1);
                        if v_isShared_2161_ == 0 {
                            leanh::lean_ctor_set(v___x_2160_, 0, v_a_2170_);
                            v___x_2172_ = v___x_2160_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2173_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2170_);
                            v___x_2172_ = v_reuseFailAlloc_2173_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2174_ = leanh::lean_ctor_get(v___x_2169_, 0);
                        leanh::lean_inc(v_a_2174_);
                        leanh::lean_dec_ref_known(v___x_2169_, 1);
                        if v_isShared_2161_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2160_, 0);
                            leanh::lean_ctor_set(v___x_2160_, 0, v_a_2174_);
                            v___x_2176_ = v___x_2160_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2177_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2174_);
                            v___x_2176_ = v_reuseFailAlloc_2177_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2160_);
                    leanh::lean_dec(v_a_2158_);
                    leanh::lean_dec_ref(v___f_2145_);
                    v___x_2178_ = l_Std_Async_Signal_Waiter_selector___lam__2___closed__2;
                    return v___x_2178_;
                }
            }
            4 => {
                v___x_2164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2164_, 0, v_val_2163_);
                v___x_2165_ = leanh::lean_unsigned_to_nat(0);
                v___x_2166_ = (leanh::lean_unbox(v_a_2158_) as u8);
                leanh::lean_dec(v_a_2158_);
                v___x_2167_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___f_2180_: *mut leanh::LeanObject,
    mut v_s_2181_: *mut leanh::LeanObject,
    mut v_x_2182_: *mut leanh::LeanObject,
    mut v___y_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Std_Async_Signal_Waiter_selector___lam__2(v___f_2180_, v_s_2181_, v_x_2182_);
    leanh::lean_dec(v_s_2181_);
    return v_res_2184_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__3(
    mut v_x_2185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2185_) == 0 {
        let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2186_ = leanh::lean_ctor_get(v_x_2185_, 0);
        leanh::lean_inc(v_a_2186_);
        leanh::lean_dec_ref_known(v_x_2185_, 1);
        v___x_2187_ = lean_task_pure(v_a_2186_);
        return v___x_2187_;
    } else {
        let mut v_a_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2188_ = leanh::lean_ctor_get(v_x_2185_, 0);
        leanh::lean_inc_ref(v_a_2188_);
        leanh::lean_dec_ref_known(v_x_2185_, 1);
        return v_a_2188_;
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__5(
    mut v_s_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2198_: u8 = 0;
    let mut v___f_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_a_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2194_ = lean_uv_signal_next(v_s_2189_);
                if leanh::lean_obj_tag(v___x_2194_) == 0 {
                    v_a_2195_ = leanh::lean_ctor_get(v___x_2194_, 0);
                    v_isSharedCheck_2207_ = (!leanh::lean_is_exclusive(v___x_2194_)) as u8;
                    if v_isSharedCheck_2207_ == 0 {
                        v___x_2197_ = v___x_2194_;
                        v_isShared_2198_ = v_isSharedCheck_2207_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2195_);
                        leanh::lean_dec(v___x_2194_);
                        v___x_2197_ = leanh::lean_box(0);
                        v_isShared_2198_ = v_isSharedCheck_2207_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2208_ = leanh::lean_ctor_get(v___x_2194_, 0);
                    v_isSharedCheck_2215_ = (!leanh::lean_is_exclusive(v___x_2194_)) as u8;
                    if v_isSharedCheck_2215_ == 0 {
                        v___x_2210_ = v___x_2194_;
                        v_isShared_2211_ = v_isSharedCheck_2215_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2208_);
                        leanh::lean_dec(v___x_2194_);
                        v___x_2210_ = leanh::lean_box(0);
                        v_isShared_2211_ = v_isSharedCheck_2215_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2193_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2193_, 0, v_val_2192_);
                return v___x_2193_;
            }
            2 => {
                v___f_2199_ = l_Std_Async_Signal_Waiter_wait___closed__1;
                v___x_2200_ = lean_io_promise_result_opt(v_a_2195_);
                leanh::lean_dec(v_a_2195_);
                v___x_2201_ = leanh::lean_unsigned_to_nat(0);
                v___x_2202_ = 1;
                v___x_2203_ = lean_task_map(v___f_2199_, v___x_2200_, v___x_2201_, v___x_2202_);
                if v_isShared_2198_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2197_, 1);
                    leanh::lean_ctor_set(v___x_2197_, 0, v___x_2203_);
                    v___x_2205_ = v___x_2197_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
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
                    leanh::lean_ctor_set_tag(v___x_2210_, 0);
                    v___x_2213_ = v___x_2210_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
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
    mut v_s_2216_: *mut leanh::LeanObject,
    mut v___y_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_Std_Async_Signal_Waiter_selector___lam__5(v_s_2216_);
    leanh::lean_dec(v_s_2216_);
    return v_res_2218_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__4(
    mut v___f_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2221_ = leanh::lean_apply_1(v___f_2219_, leanh::lean_box(0));
    return v___x_2221_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__4___boxed(
    mut v___f_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Std_Async_Signal_Waiter_selector___lam__4(v___f_2222_);
    return v_res_2224_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__6(
    mut v___x_2225_: *mut leanh::LeanObject,
    mut v___f_2226_: *mut leanh::LeanObject,
    mut v_x_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_a_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: u8 = 0;
    let mut v_val_2244_: u8 = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: u8 = 0;
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2227_) == 0 {
                    leanh::lean_dec_ref(v___f_2226_);
                    leanh::lean_dec(v___x_2225_);
                    v_a_2229_ = leanh::lean_ctor_get(v_x_2227_, 0);
                    v_isSharedCheck_2237_ = (!leanh::lean_is_exclusive(v_x_2227_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2231_ = v_x_2227_;
                        v_isShared_2232_ = v_isSharedCheck_2237_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2229_);
                        leanh::lean_dec(v_x_2227_);
                        v___x_2231_ = leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2237_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2238_ = leanh::lean_ctor_get(v_x_2227_, 0);
                    v_isSharedCheck_2254_ = (!leanh::lean_is_exclusive(v_x_2227_)) as u8;
                    if v_isSharedCheck_2254_ == 0 {
                        v___x_2240_ = v_x_2227_;
                        v_isShared_2241_ = v_isSharedCheck_2254_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2238_);
                        leanh::lean_dec(v_x_2227_);
                        v___x_2240_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2235_, 0, v___x_2234_);
                return v___x_2235_;
            }
            3 => {
                v___x_2242_ = lean_io_get_task_state(v_a_2238_);
                leanh::lean_dec(v_a_2238_);
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
                v___x_2245_ = leanh::lean_box((v_val_2244_) as usize);
                if v_isShared_2241_ == 0 {
                    leanh::lean_ctor_set(v___x_2240_, 0, v___x_2245_);
                    v___x_2247_ = v___x_2240_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2245_);
                    v___x_2247_ = v_reuseFailAlloc_2251_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2248_, 0, v___x_2247_);
                v___x_2249_ = 0;
                v___x_2250_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___x_2255_: *mut leanh::LeanObject,
    mut v___f_2256_: *mut leanh::LeanObject,
    mut v_x_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2259_ = l_Std_Async_Signal_Waiter_selector___lam__6(v___x_2255_, v___f_2256_, v_x_2257_);
    return v_res_2259_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__7(
    mut v___f_2260_: *mut leanh::LeanObject,
    mut v___x_2261_: *mut leanh::LeanObject,
    mut v___f_2262_: *mut leanh::LeanObject,
    mut v___f_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v___x_2261_, 2);
    v___x_2265_ = lean_io_as_task(v___f_2260_, v___x_2261_);
    v___x_2266_ = 1;
    v___x_2267_ = lean_task_bind(v___x_2265_, v___f_2262_, v___x_2261_, v___x_2266_);
    v___x_2268_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    v___x_2269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2269_, 0, v___x_2268_);
    v___x_2270_ = 0;
    v___x_2271_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2261_,
        v___x_2270_,
        v___x_2269_,
        v___f_2263_,
    );
    return v___x_2271_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__7___boxed(
    mut v___f_2272_: *mut leanh::LeanObject,
    mut v___x_2273_: *mut leanh::LeanObject,
    mut v___f_2274_: *mut leanh::LeanObject,
    mut v___f_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Std_Async_Signal_Waiter_selector___lam__7(
        v___f_2272_,
        v___x_2273_,
        v___f_2274_,
        v___f_2275_,
    );
    return v_res_2277_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__8(
    mut v___x_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2280_, 0, v___x_2278_);
    return v___x_2280_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__8___boxed(
    mut v___x_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ = l_Std_Async_Signal_Waiter_selector___lam__8(v___x_2281_);
    return v_res_2283_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__9(
    mut v_waiter_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___f_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_unused_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2287_) == 0 {
                    v_a_2292_ = leanh::lean_ctor_get(v_a_2287_, 0);
                    leanh::lean_inc(v_a_2292_);
                    leanh::lean_dec_ref_known(v_a_2287_, 1);
                    v_a_2290_ = v_a_2292_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_2303_ = (!leanh::lean_is_exclusive(v_a_2287_)) as u8;
                    if v_isSharedCheck_2303_ == 0 {
                        v_unused_2304_ = leanh::lean_ctor_get(v_a_2287_, 0);
                        leanh::lean_dec(v_unused_2304_);
                        v___x_2294_ = v_a_2287_;
                        v_isShared_2295_ = v_isSharedCheck_2303_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2287_);
                        v___x_2294_ = leanh::lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2303_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2291_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2291_, 0, v_a_2290_);
                return v___x_2291_;
            }
            2 => {
                v___f_2296_ = l_Std_Async_Signal_Waiter_selector___lam__9___closed__0;
                v___x_2297_ =
                    l_Std_Async_Waiter_race___at___00Std_Async_Signal_Waiter_selector_spec__0(
                        v_waiter_2286_,
                        v___f_2296_,
                    );
                if leanh::lean_obj_tag(v___x_2297_) == 0 {
                    v_a_2298_ = leanh::lean_ctor_get(v___x_2297_, 0);
                    leanh::lean_inc(v_a_2298_);
                    leanh::lean_dec_ref_known(v___x_2297_, 1);
                    if v_isShared_2295_ == 0 {
                        leanh::lean_ctor_set(v___x_2294_, 0, v_a_2298_);
                        v___x_2300_ = v___x_2294_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2301_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2298_);
                        v___x_2300_ = v_reuseFailAlloc_2301_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2294_);
                    v_a_2302_ = leanh::lean_ctor_get(v___x_2297_, 0);
                    leanh::lean_inc(v_a_2302_);
                    leanh::lean_dec_ref_known(v___x_2297_, 1);
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
    mut v_waiter_2305_: *mut leanh::LeanObject,
    mut v_a_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2308_ = l_Std_Async_Signal_Waiter_selector___lam__9(v_waiter_2305_, v_a_2306_);
    leanh::lean_dec_ref(v_waiter_2305_);
    return v_res_2308_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__10(
    mut v___f_2311_: *mut leanh::LeanObject,
    mut v___x_2312_: *mut leanh::LeanObject,
    mut v_x_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_a_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2313_) == 0 {
                    leanh::lean_dec(v___x_2312_);
                    leanh::lean_dec_ref(v___f_2311_);
                    v_a_2315_ = leanh::lean_ctor_get(v_x_2313_, 0);
                    v_isSharedCheck_2323_ = (!leanh::lean_is_exclusive(v_x_2313_)) as u8;
                    if v_isSharedCheck_2323_ == 0 {
                        v___x_2317_ = v_x_2313_;
                        v_isShared_2318_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2315_);
                        leanh::lean_dec(v_x_2313_);
                        v___x_2317_ = leanh::lean_box(0);
                        v_isShared_2318_ = v_isSharedCheck_2323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2324_ = leanh::lean_ctor_get(v_x_2313_, 0);
                    leanh::lean_inc(v_a_2324_);
                    leanh::lean_dec_ref_known(v_x_2313_, 1);
                    v___x_2325_ = 0;
                    v___x_2326_ =
                        lean_io_map_task(v___f_2311_, v_a_2324_, v___x_2312_, v___x_2325_);
                    leanh::lean_dec_ref(v___x_2326_);
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
                    v_reuseFailAlloc_2322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2315_);
                    v___x_2320_ = v_reuseFailAlloc_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2321_, 0, v___x_2320_);
                return v___x_2321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__10___boxed(
    mut v___f_2328_: *mut leanh::LeanObject,
    mut v___x_2329_: *mut leanh::LeanObject,
    mut v_x_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ = l_Std_Async_Signal_Waiter_selector___lam__10(v___f_2328_, v___x_2329_, v_x_2330_);
    return v_res_2332_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__11(
    mut v___f_2333_: *mut leanh::LeanObject,
    mut v___x_2334_: *mut leanh::LeanObject,
    mut v_waiter_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = leanh::lean_apply_1(v___f_2333_, leanh::lean_box(0));
    v___f_2338_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__9___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2338_, 0, v_waiter_2335_);
    leanh::lean_inc(v___x_2334_);
    v___f_2339_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__10___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2339_, 0, v___f_2338_);
    leanh::lean_closure_set(v___f_2339_, 1, v___x_2334_);
    v___x_2340_ = 0;
    v___x_2341_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2334_,
        v___x_2340_,
        v___x_2337_,
        v___f_2339_,
    );
    return v___x_2341_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector___lam__11___boxed(
    mut v___f_2342_: *mut leanh::LeanObject,
    mut v___x_2343_: *mut leanh::LeanObject,
    mut v_waiter_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2346_ =
        l_Std_Async_Signal_Waiter_selector___lam__11(v___f_2342_, v___x_2343_, v_waiter_2344_);
    return v_res_2346_;
}
pub unsafe fn l_Std_Async_Signal_Waiter_selector(
    mut v_s_2349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_s_2349_, 2);
    v___f_2350_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2350_, 0, v_s_2349_);
    v___f_2351_ = l_Std_Async_Signal_Waiter_selector___closed__0;
    v___f_2352_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2352_, 0, v___f_2351_);
    leanh::lean_closure_set(v___f_2352_, 1, v_s_2349_);
    v___f_2353_ = l_Std_Async_Signal_Waiter_selector___closed__1;
    v___f_2354_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__5___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2354_, 0, v_s_2349_);
    leanh::lean_inc_ref(v___f_2354_);
    v___f_2355_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2355_, 0, v___f_2354_);
    v___x_2356_ = leanh::lean_unsigned_to_nat(0);
    v___f_2357_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2357_, 0, v___x_2356_);
    leanh::lean_closure_set(v___f_2357_, 1, v___f_2352_);
    v___f_2358_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__7___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2358_, 0, v___f_2355_);
    leanh::lean_closure_set(v___f_2358_, 1, v___x_2356_);
    leanh::lean_closure_set(v___f_2358_, 2, v___f_2353_);
    leanh::lean_closure_set(v___f_2358_, 3, v___f_2357_);
    v___f_2359_ = leanh::lean_alloc_closure(
        l_Std_Async_Signal_Waiter_selector___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2359_, 0, v___f_2354_);
    leanh::lean_closure_set(v___f_2359_, 1, v___x_2356_);
    v___x_2360_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2360_, 0, v___f_2358_);
    leanh::lean_ctor_set(v___x_2360_, 1, v___f_2359_);
    leanh::lean_ctor_set(v___x_2360_, 2, v___f_2350_);
    return v___x_2360_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_Signal(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_Signal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_Signal(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_Signal(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_UV_Signal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Signal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_Signal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Async_Signal(builtin);
}