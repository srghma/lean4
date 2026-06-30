// Lean compiler output
// Module: Lean.Server.ServerTask
// Imports: Init.Task Init.System.IO
use crate::ffi::{
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_io_as_task, lean_io_bind_task,
    lean_io_cancel, lean_io_get_task_state, lean_io_map_task, lean_io_wait, lean_io_wait_any,
    lean_string_utf8_byte_size, lean_task_bind, lean_task_get_own, lean_task_map, lean_task_pure,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::Task::{initialize_Init_Task, runtime_initialize_Init_Task};
pub static l_Lean_Server_instCoeTaskServerTask___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Server_instCoeTaskServerTask___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instCoeTaskServerTask___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instCoeTaskServerTask___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_join___redArg___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_ServerTask_join___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_join___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_ServerTask_join___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_ServerTask_join___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value)
            as *mut leanh::LeanObject,
        14997215300048349804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value)
            as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
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
        78, 97, 116, 46, 122, 101, 114, 111, 95, 108, 116, 95, 115, 117, 99, 99, 0,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [122, 101, 114, 111, 95, 108, 116, 95, 115, 117, 99, 99, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value)
            as *mut leanh::LeanObject,
        3679434288154086795 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 108, 101, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value)
            as *mut leanh::LeanObject,
        3984140175429830279 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [95, 0],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__31: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__35: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__38: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__41: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Server_ServerTask_waitAny___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Server_instInhabitedServerTask_default___redArg(
    mut v_inst_801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = lean_task_pure(v_inst_801_);
    return v___x_802_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerTask_default(
    mut v_00_u03b1_803_: *mut leanh::LeanObject,
    mut v_inst_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = lean_task_pure(v_inst_804_);
    return v___x_805_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerTask___redArg(
    mut v_inst_806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = lean_task_pure(v_inst_806_);
    return v___x_807_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerTask(
    mut v_a_808_: *mut leanh::LeanObject,
    mut v_inst_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = lean_task_pure(v_inst_809_);
    return v___x_810_;
}
pub unsafe fn l_Lean_Server_instCoeTaskServerTask___lam__0(
    mut v_task_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_task_811_);
    return v_task_811_;
}
pub unsafe fn l_Lean_Server_instCoeTaskServerTask___lam__0___boxed(
    mut v_task_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_Server_instCoeTaskServerTask___lam__0(v_task_812_);
    leanh::lean_dec_ref(v_task_812_);
    return v_res_813_;
}
pub unsafe fn l_Lean_Server_instCoeTaskServerTask(
    mut v_00_u03b1_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_816_ = l_Lean_Server_instCoeTaskServerTask___closed__0;
    return v___f_816_;
}
pub unsafe fn l_Lean_Server_ServerTask_pure___redArg(
    mut v_x_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = lean_task_pure(v_x_817_);
    return v___x_818_;
}
pub unsafe fn l_Lean_Server_ServerTask_pure(
    mut v_00_u03b1_819_: *mut leanh::LeanObject,
    mut v_x_820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = lean_task_pure(v_x_820_);
    return v___x_821_;
}
pub unsafe fn l_Lean_Server_ServerTask_get___redArg(
    mut v_t_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = lean_task_get_own(v_t_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Server_ServerTask_get(
    mut v_00_u03b1_824_: *mut leanh::LeanObject,
    mut v_t_825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = lean_task_get_own(v_t_825_);
    return v___x_826_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait___redArg(
    mut v_t_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = lean_io_wait(v_t_827_);
    return v___x_829_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait___redArg___boxed(
    mut v_t_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lean_Server_ServerTask_wait___redArg(v_t_830_);
    return v_res_832_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait(
    mut v_00_u03b1_833_: *mut leanh::LeanObject,
    mut v_t_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = lean_io_wait(v_t_834_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait___boxed(
    mut v_00_u03b1_837_: *mut leanh::LeanObject,
    mut v_t_838_: *mut leanh::LeanObject,
    mut v_a_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Lean_Server_ServerTask_wait(v_00_u03b1_837_, v_t_838_);
    return v_res_840_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCheap___redArg(
    mut v_f_841_: *mut leanh::LeanObject,
    mut v_t_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = leanh::lean_unsigned_to_nat(0);
    v___x_844_ = 1;
    v___x_845_ = lean_task_map(v_f_841_, v_t_842_, v___x_843_, v___x_844_);
    return v___x_845_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCheap(
    mut v_00_u03b1_846_: *mut leanh::LeanObject,
    mut v_00_u03b2_847_: *mut leanh::LeanObject,
    mut v_f_848_: *mut leanh::LeanObject,
    mut v_t_849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = l_Lean_Server_ServerTask_mapCheap___redArg(v_f_848_, v_t_849_);
    return v___x_850_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCostly___redArg(
    mut v_f_851_: *mut leanh::LeanObject,
    mut v_t_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = leanh::lean_unsigned_to_nat(9);
    v___x_854_ = 0;
    v___x_855_ = lean_task_map(v_f_851_, v_t_852_, v___x_853_, v___x_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCostly(
    mut v_00_u03b1_856_: *mut leanh::LeanObject,
    mut v_00_u03b2_857_: *mut leanh::LeanObject,
    mut v_f_858_: *mut leanh::LeanObject,
    mut v_t_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_Server_ServerTask_mapCostly___redArg(v_f_858_, v_t_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(
    mut v_f_861_: *mut leanh::LeanObject,
    mut v_x_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = leanh::lean_apply_1(v_f_861_, v_x_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCheap___redArg(
    mut v_t_864_: *mut leanh::LeanObject,
    mut v_f_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_866_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_bindCheap___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_866_, 0, v_f_865_);
    v___x_867_ = leanh::lean_unsigned_to_nat(0);
    v___x_868_ = 1;
    v___x_869_ = lean_task_bind(v_t_864_, v___f_866_, v___x_867_, v___x_868_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCheap(
    mut v_00_u03b1_870_: *mut leanh::LeanObject,
    mut v_00_u03b2_871_: *mut leanh::LeanObject,
    mut v_t_872_: *mut leanh::LeanObject,
    mut v_f_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_t_872_, v_f_873_);
    return v___x_874_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCostly___redArg(
    mut v_t_875_: *mut leanh::LeanObject,
    mut v_f_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_877_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_bindCheap___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_877_, 0, v_f_876_);
    v___x_878_ = leanh::lean_unsigned_to_nat(9);
    v___x_879_ = 0;
    v___x_880_ = lean_task_bind(v_t_875_, v___f_877_, v___x_878_, v___x_879_);
    return v___x_880_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCostly(
    mut v_00_u03b1_881_: *mut leanh::LeanObject,
    mut v_00_u03b2_882_: *mut leanh::LeanObject,
    mut v_t_883_: *mut leanh::LeanObject,
    mut v_f_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lean_Server_ServerTask_bindCostly___redArg(v_t_883_, v_f_884_);
    return v___x_885_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(
    mut v_acc_886_: *mut leanh::LeanObject,
    mut v_x_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = lean_array_push(v_acc_886_, v_x_887_);
    return v___x_888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(
    mut v_a_889_: *mut leanh::LeanObject,
    mut v_acc_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_891_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_891_, 0, v_acc_890_);
    v___x_892_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_891_, v_a_889_);
    return v___x_892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(
    mut v_as_893_: *mut leanh::LeanObject,
    mut v_sz_894_: usize,
    mut v_i_895_: usize,
    mut v_b_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_897_: u8 = 0;
    let mut v_a_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: usize = 0;
    let mut v___x_902_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_897_ = lean_usize_dec_lt(v_i_895_, v_sz_894_);
                if v___x_897_ == 0 {
                    return v_b_896_;
                } else {
                    v_a_898_ = lean_array_uget_borrowed(v_as_893_, v_i_895_);
                    leanh::lean_inc(v_a_898_);
                    v___f_899_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_899_, 0, v_a_898_);
                    v___x_900_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_b_896_, v___f_899_);
                    v___x_901_ = 1usize;
                    v___x_902_ = lean_usize_add(v_i_895_, v___x_901_);
                    v_i_895_ = v___x_902_;
                    v_b_896_ = v___x_900_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___boxed(
    mut v_as_904_: *mut leanh::LeanObject,
    mut v_sz_905_: *mut leanh::LeanObject,
    mut v_i_906_: *mut leanh::LeanObject,
    mut v_b_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_908_: usize = 0;
    let mut v_i_boxed_909_: usize = 0;
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_908_ = leanh::lean_unbox_usize(v_sz_905_);
    leanh::lean_dec(v_sz_905_);
    v_i_boxed_909_ = leanh::lean_unbox_usize(v_i_906_);
    leanh::lean_dec(v_i_906_);
    v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_904_, v_sz_boxed_908_, v_i_boxed_909_, v_b_907_);
    leanh::lean_dec_ref(v_as_904_);
    return v_res_910_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_join___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_Server_ServerTask_join___redArg___closed__0;
    v_r_914_ = lean_task_pure(v___x_913_);
    return v_r_914_;
}
pub unsafe fn l_Lean_Server_ServerTask_join___redArg(
    mut v_ts_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_917_: usize = 0;
    let mut v___x_918_: usize = 0;
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_916_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_join___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_join___redArg___closed__1_once),
        _init_l_Lean_Server_ServerTask_join___redArg___closed__1,
    );
    v_sz_917_ = lean_array_size(v_ts_915_);
    v___x_918_ = 0usize;
    v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_ts_915_, v_sz_917_, v___x_918_, v_r_916_);
    return v___x_919_;
}
pub unsafe fn l_Lean_Server_ServerTask_join___redArg___boxed(
    mut v_ts_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Lean_Server_ServerTask_join___redArg(v_ts_920_);
    leanh::lean_dec_ref(v_ts_920_);
    return v_res_921_;
}
pub unsafe fn l_Lean_Server_ServerTask_join(
    mut v_00_u03b1_922_: *mut leanh::LeanObject,
    mut v_ts_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Lean_Server_ServerTask_join___redArg(v_ts_923_);
    return v___x_924_;
}
pub unsafe fn l_Lean_Server_ServerTask_join___boxed(
    mut v_00_u03b1_925_: *mut leanh::LeanObject,
    mut v_ts_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ = l_Lean_Server_ServerTask_join(v_00_u03b1_925_, v_ts_926_);
    leanh::lean_dec_ref(v_ts_926_);
    return v_res_927_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(
    mut v_00_u03b1_928_: *mut leanh::LeanObject,
    mut v_as_929_: *mut leanh::LeanObject,
    mut v_sz_930_: usize,
    mut v_i_931_: usize,
    mut v_b_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_929_, v_sz_930_, v_i_931_, v_b_932_);
    return v___x_933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(
    mut v_00_u03b1_934_: *mut leanh::LeanObject,
    mut v_as_935_: *mut leanh::LeanObject,
    mut v_sz_936_: *mut leanh::LeanObject,
    mut v_i_937_: *mut leanh::LeanObject,
    mut v_b_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_939_: usize = 0;
    let mut v_i_boxed_940_: usize = 0;
    let mut v_res_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_939_ = leanh::lean_unbox_usize(v_sz_936_);
    leanh::lean_dec(v_sz_936_);
    v_i_boxed_940_ = leanh::lean_unbox_usize(v_i_937_);
    leanh::lean_dec(v_i_937_);
    v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(v_00_u03b1_934_, v_as_935_, v_sz_boxed_939_, v_i_boxed_940_, v_b_938_);
    leanh::lean_dec_ref(v_as_935_);
    return v_res_941_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask___redArg(
    mut v_act_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = leanh::lean_unsigned_to_nat(9);
    v___x_945_ = lean_io_as_task(v_act_942_, v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(
    mut v_act_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_946_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask(
    mut v_00_u03b1_949_: *mut leanh::LeanObject,
    mut v_act_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_950_);
    return v___x_952_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask___boxed(
    mut v_00_u03b1_953_: *mut leanh::LeanObject,
    mut v_act_954_: *mut leanh::LeanObject,
    mut v_a_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_Server_ServerTask_BaseIO_asTask(v_00_u03b1_953_, v_act_954_);
    return v_res_956_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(
    mut v_f_957_: *mut leanh::LeanObject,
    mut v_t_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u8 = 0;
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = leanh::lean_unsigned_to_nat(0);
    v___x_961_ = 1;
    v___x_962_ = lean_io_map_task(v_f_957_, v_t_958_, v___x_960_, v___x_961_);
    return v___x_962_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(
    mut v_f_963_: *mut leanh::LeanObject,
    mut v_t_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_963_, v_t_964_);
    return v_res_966_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(
    mut v_00_u03b1_967_: *mut leanh::LeanObject,
    mut v_00_u03b2_968_: *mut leanh::LeanObject,
    mut v_f_969_: *mut leanh::LeanObject,
    mut v_t_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_969_, v_t_970_);
    return v___x_972_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(
    mut v_00_u03b1_973_: *mut leanh::LeanObject,
    mut v_00_u03b2_974_: *mut leanh::LeanObject,
    mut v_f_975_: *mut leanh::LeanObject,
    mut v_t_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(
        v_00_u03b1_973_,
        v_00_u03b2_974_,
        v_f_975_,
        v_t_976_,
    );
    return v_res_978_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(
    mut v_f_979_: *mut leanh::LeanObject,
    mut v_t_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = leanh::lean_unsigned_to_nat(9);
    v___x_983_ = 0;
    v___x_984_ = lean_io_map_task(v_f_979_, v_t_980_, v___x_982_, v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(
    mut v_f_985_: *mut leanh::LeanObject,
    mut v_t_986_: *mut leanh::LeanObject,
    mut v_a_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_985_, v_t_986_);
    return v_res_988_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(
    mut v_00_u03b1_989_: *mut leanh::LeanObject,
    mut v_00_u03b2_990_: *mut leanh::LeanObject,
    mut v_f_991_: *mut leanh::LeanObject,
    mut v_t_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_991_, v_t_992_);
    return v___x_994_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(
    mut v_00_u03b1_995_: *mut leanh::LeanObject,
    mut v_00_u03b2_996_: *mut leanh::LeanObject,
    mut v_f_997_: *mut leanh::LeanObject,
    mut v_t_998_: *mut leanh::LeanObject,
    mut v_a_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(
        v_00_u03b1_995_,
        v_00_u03b2_996_,
        v_f_997_,
        v_t_998_,
    );
    return v_res_1000_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(
    mut v_f_1001_: *mut leanh::LeanObject,
    mut v_x_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = leanh::lean_apply_2(v_f_1001_, v_x_1002_, leanh::lean_box(0));
    return v___x_1004_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(
    mut v_f_1005_: *mut leanh::LeanObject,
    mut v_x_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ =
        l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(v_f_1005_, v_x_1006_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(
    mut v_t_1009_: *mut leanh::LeanObject,
    mut v_f_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1012_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1012_, 0, v_f_1010_);
    v___x_1013_ = leanh::lean_unsigned_to_nat(0);
    v___x_1014_ = 1;
    v___x_1015_ = lean_io_bind_task(v_t_1009_, v___f_1012_, v___x_1013_, v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(
    mut v_t_1016_: *mut leanh::LeanObject,
    mut v_f_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_1016_, v_f_1017_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(
    mut v_00_u03b1_1020_: *mut leanh::LeanObject,
    mut v_00_u03b2_1021_: *mut leanh::LeanObject,
    mut v_t_1022_: *mut leanh::LeanObject,
    mut v_f_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_1022_, v_f_1023_);
    return v___x_1025_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(
    mut v_00_u03b1_1026_: *mut leanh::LeanObject,
    mut v_00_u03b2_1027_: *mut leanh::LeanObject,
    mut v_t_1028_: *mut leanh::LeanObject,
    mut v_f_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(
        v_00_u03b1_1026_,
        v_00_u03b2_1027_,
        v_t_1028_,
        v_f_1029_,
    );
    return v_res_1031_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(
    mut v_t_1032_: *mut leanh::LeanObject,
    mut v_f_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1035_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1035_, 0, v_f_1033_);
    v___x_1036_ = leanh::lean_unsigned_to_nat(9);
    v___x_1037_ = 0;
    v___x_1038_ = lean_io_bind_task(v_t_1032_, v___f_1035_, v___x_1036_, v___x_1037_);
    return v___x_1038_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(
    mut v_t_1039_: *mut leanh::LeanObject,
    mut v_f_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_1039_, v_f_1040_);
    return v_res_1042_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(
    mut v_00_u03b1_1043_: *mut leanh::LeanObject,
    mut v_00_u03b2_1044_: *mut leanh::LeanObject,
    mut v_t_1045_: *mut leanh::LeanObject,
    mut v_f_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_1045_, v_f_1046_);
    return v___x_1048_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(
    mut v_00_u03b1_1049_: *mut leanh::LeanObject,
    mut v_00_u03b2_1050_: *mut leanh::LeanObject,
    mut v_t_1051_: *mut leanh::LeanObject,
    mut v_f_1052_: *mut leanh::LeanObject,
    mut v_a_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(
        v_00_u03b1_1049_,
        v_00_u03b2_1050_,
        v_t_1051_,
        v_f_1052_,
    );
    return v_res_1054_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(
    mut v_act_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1061_: u8 = 0;
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1065_: u8 = 0;
    let mut v_a_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1057_ = leanh::lean_apply_1(v_act_1055_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1057_) == 0 {
                    v_a_1058_ = leanh::lean_ctor_get(v___x_1057_, 0);
                    v_isSharedCheck_1065_ = (!leanh::lean_is_exclusive(v___x_1057_)) as u8;
                    if v_isSharedCheck_1065_ == 0 {
                        v___x_1060_ = v___x_1057_;
                        v_isShared_1061_ = v_isSharedCheck_1065_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1058_);
                        leanh::lean_dec(v___x_1057_);
                        v___x_1060_ = leanh::lean_box(0);
                        v_isShared_1061_ = v_isSharedCheck_1065_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1066_ = leanh::lean_ctor_get(v___x_1057_, 0);
                    v_isSharedCheck_1073_ = (!leanh::lean_is_exclusive(v___x_1057_)) as u8;
                    if v_isSharedCheck_1073_ == 0 {
                        v___x_1068_ = v___x_1057_;
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1066_);
                        leanh::lean_dec(v___x_1057_);
                        v___x_1068_ = leanh::lean_box(0);
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1061_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1060_, 1);
                    v___x_1063_ = v___x_1060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1064_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
                    v___x_1063_ = v_reuseFailAlloc_1064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1063_;
            }
            3 => {
                if v_isShared_1069_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1068_, 0);
                    v___x_1071_ = v___x_1068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
                    v___x_1071_ = v_reuseFailAlloc_1072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed(
    mut v_act_1074_: *mut leanh::LeanObject,
    mut v___y_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1076_ = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(v_act_1074_);
    return v_res_1076_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg(
    mut v_act_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1079_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1079_, 0, v_act_1077_);
    v___x_1080_ = leanh::lean_unsigned_to_nat(9);
    v___x_1081_ = lean_io_as_task(v___f_1079_, v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(
    mut v_act_1082_: *mut leanh::LeanObject,
    mut v_a_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_1082_);
    return v_res_1084_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask(
    mut v_00_u03b5_1085_: *mut leanh::LeanObject,
    mut v_00_u03b1_1086_: *mut leanh::LeanObject,
    mut v_act_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_1087_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___boxed(
    mut v_00_u03b5_1090_: *mut leanh::LeanObject,
    mut v_00_u03b1_1091_: *mut leanh::LeanObject,
    mut v_act_1092_: *mut leanh::LeanObject,
    mut v_a_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1094_ =
        l_Lean_Server_ServerTask_EIO_asTask(v_00_u03b5_1090_, v_00_u03b1_1091_, v_act_1092_);
    return v_res_1094_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(
    mut v_f_1095_: *mut leanh::LeanObject,
    mut v_a_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut v_a_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1098_ =
                    leanh::lean_apply_2(v_f_1095_, v_a_1096_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1098_) == 0 {
                    v_a_1099_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1106_ = (!leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1106_ == 0 {
                        v___x_1101_ = v___x_1098_;
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1099_);
                        leanh::lean_dec(v___x_1098_);
                        v___x_1101_ = leanh::lean_box(0);
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1107_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1114_ = (!leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1114_ == 0 {
                        v___x_1109_ = v___x_1098_;
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1107_);
                        leanh::lean_dec(v___x_1098_);
                        v___x_1109_ = leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1102_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1101_, 1);
                    v___x_1104_ = v___x_1101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1104_;
            }
            3 => {
                if v_isShared_1110_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1109_, 0);
                    v___x_1112_ = v___x_1109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
                    v___x_1112_ = v_reuseFailAlloc_1113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed(
    mut v_f_1115_: *mut leanh::LeanObject,
    mut v_a_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(v_f_1115_, v_a_1116_);
    return v_res_1118_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(
    mut v_f_1119_: *mut leanh::LeanObject,
    mut v_t_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1122_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1122_, 0, v_f_1119_);
    v___x_1123_ = leanh::lean_unsigned_to_nat(0);
    v___x_1124_ = 1;
    v___x_1125_ = lean_io_map_task(v___f_1122_, v_t_1120_, v___x_1123_, v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(
    mut v_f_1126_: *mut leanh::LeanObject,
    mut v_t_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_1126_, v_t_1127_);
    return v_res_1129_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap(
    mut v_00_u03b1_1130_: *mut leanh::LeanObject,
    mut v_00_u03b5_1131_: *mut leanh::LeanObject,
    mut v_00_u03b2_1132_: *mut leanh::LeanObject,
    mut v_f_1133_: *mut leanh::LeanObject,
    mut v_t_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_1133_, v_t_1134_);
    return v___x_1136_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(
    mut v_00_u03b1_1137_: *mut leanh::LeanObject,
    mut v_00_u03b5_1138_: *mut leanh::LeanObject,
    mut v_00_u03b2_1139_: *mut leanh::LeanObject,
    mut v_f_1140_: *mut leanh::LeanObject,
    mut v_t_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1143_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap(
        v_00_u03b1_1137_,
        v_00_u03b5_1138_,
        v_00_u03b2_1139_,
        v_f_1140_,
        v_t_1141_,
    );
    return v_res_1143_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(
    mut v_f_1144_: *mut leanh::LeanObject,
    mut v_t_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1147_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1147_, 0, v_f_1144_);
    v___x_1148_ = leanh::lean_unsigned_to_nat(9);
    v___x_1149_ = 0;
    v___x_1150_ = lean_io_map_task(v___f_1147_, v_t_1145_, v___x_1148_, v___x_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(
    mut v_f_1151_: *mut leanh::LeanObject,
    mut v_t_1152_: *mut leanh::LeanObject,
    mut v_a_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_1151_, v_t_1152_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly(
    mut v_00_u03b1_1155_: *mut leanh::LeanObject,
    mut v_00_u03b5_1156_: *mut leanh::LeanObject,
    mut v_00_u03b2_1157_: *mut leanh::LeanObject,
    mut v_f_1158_: *mut leanh::LeanObject,
    mut v_t_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_1158_, v_t_1159_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(
    mut v_00_u03b1_1162_: *mut leanh::LeanObject,
    mut v_00_u03b5_1163_: *mut leanh::LeanObject,
    mut v_00_u03b2_1164_: *mut leanh::LeanObject,
    mut v_f_1165_: *mut leanh::LeanObject,
    mut v_t_1166_: *mut leanh::LeanObject,
    mut v_a_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1168_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly(
        v_00_u03b1_1162_,
        v_00_u03b5_1163_,
        v_00_u03b2_1164_,
        v_f_1165_,
        v_t_1166_,
    );
    return v_res_1168_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(
    mut v_f_1169_: *mut leanh::LeanObject,
    mut v_a_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1172_ =
                    leanh::lean_apply_2(v_f_1169_, v_a_1170_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1172_) == 0 {
                    v_a_1173_ = leanh::lean_ctor_get(v___x_1172_, 0);
                    leanh::lean_inc(v_a_1173_);
                    leanh::lean_dec_ref_known(v___x_1172_, 1);
                    return v_a_1173_;
                } else {
                    v_a_1174_ = leanh::lean_ctor_get(v___x_1172_, 0);
                    v_isSharedCheck_1182_ = (!leanh::lean_is_exclusive(v___x_1172_)) as u8;
                    if v_isSharedCheck_1182_ == 0 {
                        v___x_1176_ = v___x_1172_;
                        v_isShared_1177_ = v_isSharedCheck_1182_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1174_);
                        leanh::lean_dec(v___x_1172_);
                        v___x_1176_ = leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1182_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1177_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1176_, 0);
                    v___x_1179_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1180_ = lean_task_pure(v___x_1179_);
                return v___x_1180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed(
    mut v_f_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(v_f_1183_, v_a_1184_);
    return v_res_1186_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(
    mut v_t_1187_: *mut leanh::LeanObject,
    mut v_f_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1190_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1190_, 0, v_f_1188_);
    v___x_1191_ = leanh::lean_unsigned_to_nat(0);
    v___x_1192_ = 1;
    v___x_1193_ = lean_io_bind_task(v_t_1187_, v___f_1190_, v___x_1191_, v___x_1192_);
    return v___x_1193_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(
    mut v_t_1194_: *mut leanh::LeanObject,
    mut v_f_1195_: *mut leanh::LeanObject,
    mut v_a_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_1194_, v_f_1195_);
    return v_res_1197_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap(
    mut v_00_u03b1_1198_: *mut leanh::LeanObject,
    mut v_00_u03b5_1199_: *mut leanh::LeanObject,
    mut v_00_u03b2_1200_: *mut leanh::LeanObject,
    mut v_t_1201_: *mut leanh::LeanObject,
    mut v_f_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_1201_, v_f_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(
    mut v_00_u03b1_1205_: *mut leanh::LeanObject,
    mut v_00_u03b5_1206_: *mut leanh::LeanObject,
    mut v_00_u03b2_1207_: *mut leanh::LeanObject,
    mut v_t_1208_: *mut leanh::LeanObject,
    mut v_f_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap(
        v_00_u03b1_1205_,
        v_00_u03b5_1206_,
        v_00_u03b2_1207_,
        v_t_1208_,
        v_f_1209_,
    );
    return v_res_1211_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(
    mut v_t_1212_: *mut leanh::LeanObject,
    mut v_f_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1215_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1215_, 0, v_f_1213_);
    v___x_1216_ = leanh::lean_unsigned_to_nat(9);
    v___x_1217_ = 0;
    v___x_1218_ = lean_io_bind_task(v_t_1212_, v___f_1215_, v___x_1216_, v___x_1217_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(
    mut v_t_1219_: *mut leanh::LeanObject,
    mut v_f_1220_: *mut leanh::LeanObject,
    mut v_a_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_1219_, v_f_1220_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly(
    mut v_00_u03b1_1223_: *mut leanh::LeanObject,
    mut v_00_u03b5_1224_: *mut leanh::LeanObject,
    mut v_00_u03b2_1225_: *mut leanh::LeanObject,
    mut v_t_1226_: *mut leanh::LeanObject,
    mut v_f_1227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_1226_, v_f_1227_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(
    mut v_00_u03b1_1230_: *mut leanh::LeanObject,
    mut v_00_u03b5_1231_: *mut leanh::LeanObject,
    mut v_00_u03b2_1232_: *mut leanh::LeanObject,
    mut v_t_1233_: *mut leanh::LeanObject,
    mut v_f_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly(
        v_00_u03b1_1230_,
        v_00_u03b5_1231_,
        v_00_u03b2_1232_,
        v_t_1233_,
        v_f_1234_,
    );
    return v_res_1236_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(
    mut v_act_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_a_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1239_ = leanh::lean_apply_1(v_act_1237_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1239_) == 0 {
                    v_a_1240_ = leanh::lean_ctor_get(v___x_1239_, 0);
                    v_isSharedCheck_1247_ = (!leanh::lean_is_exclusive(v___x_1239_)) as u8;
                    if v_isSharedCheck_1247_ == 0 {
                        v___x_1242_ = v___x_1239_;
                        v_isShared_1243_ = v_isSharedCheck_1247_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1240_);
                        leanh::lean_dec(v___x_1239_);
                        v___x_1242_ = leanh::lean_box(0);
                        v_isShared_1243_ = v_isSharedCheck_1247_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1248_ = leanh::lean_ctor_get(v___x_1239_, 0);
                    v_isSharedCheck_1255_ = (!leanh::lean_is_exclusive(v___x_1239_)) as u8;
                    if v_isSharedCheck_1255_ == 0 {
                        v___x_1250_ = v___x_1239_;
                        v_isShared_1251_ = v_isSharedCheck_1255_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1248_);
                        leanh::lean_dec(v___x_1239_);
                        v___x_1250_ = leanh::lean_box(0);
                        v_isShared_1251_ = v_isSharedCheck_1255_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1243_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1242_, 1);
                    v___x_1245_ = v___x_1242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
                    v___x_1245_ = v_reuseFailAlloc_1246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1245_;
            }
            3 => {
                if v_isShared_1251_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1250_, 0);
                    v___x_1253_ = v___x_1250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
                    v___x_1253_ = v_reuseFailAlloc_1254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed(
    mut v_act_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(v_act_1256_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___redArg(
    mut v_act_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1261_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1261_, 0, v_act_1259_);
    v___x_1262_ = leanh::lean_unsigned_to_nat(9);
    v___x_1263_ = lean_io_as_task(v___f_1261_, v___x_1262_);
    return v___x_1263_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(
    mut v_act_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_1264_);
    return v_res_1266_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask(
    mut v_00_u03b1_1267_: *mut leanh::LeanObject,
    mut v_act_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1270_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_1268_);
    return v___x_1270_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___boxed(
    mut v_00_u03b1_1271_: *mut leanh::LeanObject,
    mut v_act_1272_: *mut leanh::LeanObject,
    mut v_a_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lean_Server_ServerTask_IO_asTask(v_00_u03b1_1271_, v_act_1272_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(
    mut v_f_1275_: *mut leanh::LeanObject,
    mut v_a_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v_a_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1278_ =
                    leanh::lean_apply_2(v_f_1275_, v_a_1276_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1278_) == 0 {
                    v_a_1279_ = leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1286_ = (!leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___x_1278_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1279_);
                        leanh::lean_dec(v___x_1278_);
                        v___x_1281_ = leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1287_ = leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1294_ = (!leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1289_ = v___x_1278_;
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1287_);
                        leanh::lean_dec(v___x_1278_);
                        v___x_1289_ = leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1282_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1281_, 1);
                    v___x_1284_ = v___x_1281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1284_;
            }
            3 => {
                if v_isShared_1290_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1289_, 0);
                    v___x_1292_ = v___x_1289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
                    v___x_1292_ = v_reuseFailAlloc_1293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed(
    mut v_f_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(v_f_1295_, v_a_1296_);
    return v_res_1298_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(
    mut v_f_1299_: *mut leanh::LeanObject,
    mut v_t_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1302_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1302_, 0, v_f_1299_);
    v___x_1303_ = leanh::lean_unsigned_to_nat(0);
    v___x_1304_ = 1;
    v___x_1305_ = lean_io_map_task(v___f_1302_, v_t_1300_, v___x_1303_, v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(
    mut v_f_1306_: *mut leanh::LeanObject,
    mut v_t_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1309_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_1306_, v_t_1307_);
    return v_res_1309_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap(
    mut v_00_u03b1_1310_: *mut leanh::LeanObject,
    mut v_00_u03b2_1311_: *mut leanh::LeanObject,
    mut v_f_1312_: *mut leanh::LeanObject,
    mut v_t_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_1312_, v_t_1313_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v_00_u03b2_1317_: *mut leanh::LeanObject,
    mut v_f_1318_: *mut leanh::LeanObject,
    mut v_t_1319_: *mut leanh::LeanObject,
    mut v_a_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Lean_Server_ServerTask_IO_mapTaskCheap(
        v_00_u03b1_1316_,
        v_00_u03b2_1317_,
        v_f_1318_,
        v_t_1319_,
    );
    return v_res_1321_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(
    mut v_f_1322_: *mut leanh::LeanObject,
    mut v_t_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1325_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1325_, 0, v_f_1322_);
    v___x_1326_ = leanh::lean_unsigned_to_nat(9);
    v___x_1327_ = 0;
    v___x_1328_ = lean_io_map_task(v___f_1325_, v_t_1323_, v___x_1326_, v___x_1327_);
    return v___x_1328_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(
    mut v_f_1329_: *mut leanh::LeanObject,
    mut v_t_1330_: *mut leanh::LeanObject,
    mut v_a_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_1329_, v_t_1330_);
    return v_res_1332_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly(
    mut v_00_u03b1_1333_: *mut leanh::LeanObject,
    mut v_00_u03b2_1334_: *mut leanh::LeanObject,
    mut v_f_1335_: *mut leanh::LeanObject,
    mut v_t_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_1335_, v_t_1336_);
    return v___x_1338_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(
    mut v_00_u03b1_1339_: *mut leanh::LeanObject,
    mut v_00_u03b2_1340_: *mut leanh::LeanObject,
    mut v_f_1341_: *mut leanh::LeanObject,
    mut v_t_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Lean_Server_ServerTask_IO_mapTaskCostly(
        v_00_u03b1_1339_,
        v_00_u03b2_1340_,
        v_f_1341_,
        v_t_1342_,
    );
    return v_res_1344_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(
    mut v_f_1345_: *mut leanh::LeanObject,
    mut v_a_1346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1348_ =
                    leanh::lean_apply_2(v_f_1345_, v_a_1346_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1348_) == 0 {
                    v_a_1349_ = leanh::lean_ctor_get(v___x_1348_, 0);
                    leanh::lean_inc(v_a_1349_);
                    leanh::lean_dec_ref_known(v___x_1348_, 1);
                    return v_a_1349_;
                } else {
                    v_a_1350_ = leanh::lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1358_ = (!leanh::lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1358_ == 0 {
                        v___x_1352_ = v___x_1348_;
                        v_isShared_1353_ = v_isSharedCheck_1358_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1350_);
                        leanh::lean_dec(v___x_1348_);
                        v___x_1352_ = leanh::lean_box(0);
                        v_isShared_1353_ = v_isSharedCheck_1358_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1353_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1352_, 0);
                    v___x_1355_ = v___x_1352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1350_);
                    v___x_1355_ = v_reuseFailAlloc_1357_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1356_ = lean_task_pure(v___x_1355_);
                return v___x_1356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed(
    mut v_f_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(v_f_1359_, v_a_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(
    mut v_t_1363_: *mut leanh::LeanObject,
    mut v_f_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1366_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1366_, 0, v_f_1364_);
    v___x_1367_ = leanh::lean_unsigned_to_nat(0);
    v___x_1368_ = 1;
    v___x_1369_ = lean_io_bind_task(v_t_1363_, v___f_1366_, v___x_1367_, v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(
    mut v_t_1370_: *mut leanh::LeanObject,
    mut v_f_1371_: *mut leanh::LeanObject,
    mut v_a_1372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_1370_, v_f_1371_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap(
    mut v_00_u03b1_1374_: *mut leanh::LeanObject,
    mut v_00_u03b2_1375_: *mut leanh::LeanObject,
    mut v_t_1376_: *mut leanh::LeanObject,
    mut v_f_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_1376_, v_f_1377_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(
    mut v_00_u03b1_1380_: *mut leanh::LeanObject,
    mut v_00_u03b2_1381_: *mut leanh::LeanObject,
    mut v_t_1382_: *mut leanh::LeanObject,
    mut v_f_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Server_ServerTask_IO_bindTaskCheap(
        v_00_u03b1_1380_,
        v_00_u03b2_1381_,
        v_t_1382_,
        v_f_1383_,
    );
    return v_res_1385_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(
    mut v_t_1386_: *mut leanh::LeanObject,
    mut v_f_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1389_ = leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1389_, 0, v_f_1387_);
    v___x_1390_ = leanh::lean_unsigned_to_nat(9);
    v___x_1391_ = 0;
    v___x_1392_ = lean_io_bind_task(v_t_1386_, v___f_1389_, v___x_1390_, v___x_1391_);
    return v___x_1392_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(
    mut v_t_1393_: *mut leanh::LeanObject,
    mut v_f_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_1393_, v_f_1394_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly(
    mut v_00_u03b1_1397_: *mut leanh::LeanObject,
    mut v_00_u03b2_1398_: *mut leanh::LeanObject,
    mut v_t_1399_: *mut leanh::LeanObject,
    mut v_f_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_1399_, v_f_1400_);
    return v___x_1402_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(
    mut v_00_u03b1_1403_: *mut leanh::LeanObject,
    mut v_00_u03b2_1404_: *mut leanh::LeanObject,
    mut v_t_1405_: *mut leanh::LeanObject,
    mut v_f_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_Server_ServerTask_IO_bindTaskCostly(
        v_00_u03b1_1403_,
        v_00_u03b2_1404_,
        v_t_1405_,
        v_f_1406_,
    );
    return v_res_1408_;
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished___redArg(
    mut v_t_1409_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1411_: u8 = 0;
    v___x_1411_ = lean_io_get_task_state(v_t_1409_);
    if v___x_1411_ == 2 {
        let mut v___x_1412_: u8 = 0;
        v___x_1412_ = 1;
        return v___x_1412_;
    } else {
        let mut v___x_1413_: u8 = 0;
        v___x_1413_ = 0;
        return v___x_1413_;
    }
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished___redArg___boxed(
    mut v_t_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1416_: u8 = 0;
    let mut v_r_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_1414_);
    leanh::lean_dec_ref(v_t_1414_);
    v_r_1417_ = leanh::lean_box((v_res_1416_) as usize);
    return v_r_1417_;
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished(
    mut v_00_u03b1_1418_: *mut leanh::LeanObject,
    mut v_t_1419_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1421_: u8 = 0;
    v___x_1421_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_1419_);
    return v___x_1421_;
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished___boxed(
    mut v_00_u03b1_1422_: *mut leanh::LeanObject,
    mut v_t_1423_: *mut leanh::LeanObject,
    mut v_a_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1425_: u8 = 0;
    let mut v_r_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_Server_ServerTask_hasFinished(v_00_u03b1_1422_, v_t_1423_);
    leanh::lean_dec_ref(v_t_1423_);
    v_r_1426_ = leanh::lean_box((v_res_1425_) as usize);
    return v_r_1426_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__10;
    v___x_1454_ = l_Lean_mkAtom(v___x_1453_);
    return v___x_1454_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12,
    );
    v___x_1456_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1457_ = lean_array_push(v___x_1456_, v___x_1455_);
    return v___x_1457_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1466_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__17;
    v___x_1467_ = lean_string_utf8_byte_size(v___x_1466_);
    return v___x_1467_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18,
    );
    v___x_1469_ = leanh::lean_unsigned_to_nat(0);
    v___x_1470_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__17;
    v___x_1471_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1471_, 0, v___x_1470_);
    leanh::lean_ctor_set(v___x_1471_, 1, v___x_1469_);
    leanh::lean_ctor_set(v___x_1471_, 2, v___x_1468_);
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = leanh::lean_box(0);
    v___x_1478_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__22;
    v___x_1479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19,
    );
    v___x_1480_ = leanh::lean_box(2);
    v___x_1481_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1481_, 0, v___x_1480_);
    leanh::lean_ctor_set(v___x_1481_, 1, v___x_1479_);
    leanh::lean_ctor_set(v___x_1481_, 2, v___x_1478_);
    leanh::lean_ctor_set(v___x_1481_, 3, v___x_1477_);
    return v___x_1481_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1482_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23,
    );
    v___x_1483_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1484_ = lean_array_push(v___x_1483_, v___x_1482_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__27;
    v___x_1493_ = l_Lean_mkAtom(v___x_1492_);
    return v___x_1493_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28,
    );
    v___x_1495_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1496_ = lean_array_push(v___x_1495_, v___x_1494_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29,
    );
    v___x_1498_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__26;
    v___x_1499_ = leanh::lean_box(2);
    v___x_1500_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1500_, 0, v___x_1499_);
    leanh::lean_ctor_set(v___x_1500_, 1, v___x_1498_);
    leanh::lean_ctor_set(v___x_1500_, 2, v___x_1497_);
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30,
    );
    v___x_1502_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1503_ = lean_array_push(v___x_1502_, v___x_1501_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31,
    );
    v___x_1505_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__9;
    v___x_1506_ = leanh::lean_box(2);
    v___x_1507_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    leanh::lean_ctor_set(v___x_1507_, 1, v___x_1505_);
    leanh::lean_ctor_set(v___x_1507_, 2, v___x_1504_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32,
    );
    v___x_1509_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24,
    );
    v___x_1510_ = lean_array_push(v___x_1509_, v___x_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33,
    );
    v___x_1512_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__16;
    v___x_1513_ = leanh::lean_box(2);
    v___x_1514_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    leanh::lean_ctor_set(v___x_1514_, 1, v___x_1512_);
    leanh::lean_ctor_set(v___x_1514_, 2, v___x_1511_);
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34,
    );
    v___x_1516_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13,
    );
    v___x_1517_ = lean_array_push(v___x_1516_, v___x_1515_);
    return v___x_1517_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35,
    );
    v___x_1519_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__11;
    v___x_1520_ = leanh::lean_box(2);
    v___x_1521_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1521_, 0, v___x_1520_);
    leanh::lean_ctor_set(v___x_1521_, 1, v___x_1519_);
    leanh::lean_ctor_set(v___x_1521_, 2, v___x_1518_);
    return v___x_1521_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36,
    );
    v___x_1523_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1524_ = lean_array_push(v___x_1523_, v___x_1522_);
    return v___x_1524_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37,
    );
    v___x_1526_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__9;
    v___x_1527_ = leanh::lean_box(2);
    v___x_1528_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1528_, 0, v___x_1527_);
    leanh::lean_ctor_set(v___x_1528_, 1, v___x_1526_);
    leanh::lean_ctor_set(v___x_1528_, 2, v___x_1525_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38,
    );
    v___x_1530_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1531_ = lean_array_push(v___x_1530_, v___x_1529_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39,
    );
    v___x_1533_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__7;
    v___x_1534_ = leanh::lean_box(2);
    v___x_1535_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    leanh::lean_ctor_set(v___x_1535_, 1, v___x_1533_);
    leanh::lean_ctor_set(v___x_1535_, 2, v___x_1532_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40,
    );
    v___x_1537_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1538_ = lean_array_push(v___x_1537_, v___x_1536_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41,
    );
    v___x_1540_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__4;
    v___x_1541_ = leanh::lean_box(2);
    v___x_1542_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
    leanh::lean_ctor_set(v___x_1542_, 1, v___x_1540_);
    leanh::lean_ctor_set(v___x_1542_, 2, v___x_1539_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42,
    );
    return v___x_1543_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(
    mut v_a_1544_: *mut leanh::LeanObject,
    mut v_a_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1544_) == 0 {
                    v___x_1546_ = l_List_reverse___redArg(v_a_1545_);
                    return v___x_1546_;
                } else {
                    v_head_1547_ = leanh::lean_ctor_get(v_a_1544_, 0);
                    v_tail_1548_ = leanh::lean_ctor_get(v_a_1544_, 1);
                    v_isSharedCheck_1556_ = (!leanh::lean_is_exclusive(v_a_1544_)) as u8;
                    if v_isSharedCheck_1556_ == 0 {
                        v___x_1550_ = v_a_1544_;
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1548_);
                        leanh::lean_inc(v_head_1547_);
                        leanh::lean_dec(v_a_1544_);
                        v___x_1550_ = leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1551_ == 0 {
                    leanh::lean_ctor_set(v___x_1550_, 1, v_a_1545_);
                    v___x_1553_ = v___x_1550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_head_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_a_1545_);
                    v___x_1553_ = v_reuseFailAlloc_1555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1544_ = v_tail_1548_;
                v_a_1545_ = v___x_1553_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny___redArg(
    mut v_tasks_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = leanh::lean_box(0);
    v___x_1560_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(
        v_tasks_1557_,
        v___x_1559_,
    );
    v___x_1561_ = lean_io_wait_any(v___x_1560_);
    leanh::lean_dec(v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny___redArg___boxed(
    mut v_tasks_1562_: *mut leanh::LeanObject,
    mut v_a_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1564_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_1562_);
    return v_res_1564_;
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny(
    mut v_00_u03b1_1565_: *mut leanh::LeanObject,
    mut v_tasks_1566_: *mut leanh::LeanObject,
    mut v_h_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_1566_);
    return v___x_1569_;
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny___boxed(
    mut v_00_u03b1_1570_: *mut leanh::LeanObject,
    mut v_tasks_1571_: *mut leanh::LeanObject,
    mut v_h_1572_: *mut leanh::LeanObject,
    mut v_a_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_Server_ServerTask_waitAny(v_00_u03b1_1570_, v_tasks_1571_, v_h_1572_);
    return v_res_1574_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(
    mut v_00_u03b1_1575_: *mut leanh::LeanObject,
    mut v_a_1576_: *mut leanh::LeanObject,
    mut v_a_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1578_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(
        v_a_1576_, v_a_1577_,
    );
    return v___x_1578_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel___redArg(
    mut v_t_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = lean_io_cancel(v_t_1579_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel___redArg___boxed(
    mut v_t_1582_: *mut leanh::LeanObject,
    mut v_a_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_Server_ServerTask_cancel___redArg(v_t_1582_);
    leanh::lean_dec_ref(v_t_1582_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel(
    mut v_00_u03b1_1585_: *mut leanh::LeanObject,
    mut v_t_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = lean_io_cancel(v_t_1586_);
    return v___x_1588_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel___boxed(
    mut v_00_u03b1_1589_: *mut leanh::LeanObject,
    mut v_t_1590_: *mut leanh::LeanObject,
    mut v_a_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_Lean_Server_ServerTask_cancel(v_00_u03b1_1589_, v_t_1590_);
    leanh::lean_dec_ref(v_t_1590_);
    return v_res_1592_;
}
pub unsafe fn l_Task_asServerTask___redArg(
    mut v_t_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_t_1593_);
    return v_t_1593_;
}
pub unsafe fn l_Task_asServerTask___redArg___boxed(
    mut v_t_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ = l_Task_asServerTask___redArg(v_t_1594_);
    leanh::lean_dec_ref(v_t_1594_);
    return v_res_1595_;
}
pub unsafe fn l_Task_asServerTask(
    mut v_00_u03b1_1596_: *mut leanh::LeanObject,
    mut v_t_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_t_1597_);
    return v_t_1597_;
}
pub unsafe fn l_Task_asServerTask___boxed(
    mut v_00_u03b1_1598_: *mut leanh::LeanObject,
    mut v_t_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Task_asServerTask(v_00_u03b1_1598_, v_t_1599_);
    leanh::lean_dec_ref(v_t_1599_);
    return v_res_1600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_ServerTask(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Task(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_ServerTask(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Server_ServerTask_waitAny___auto__1 = _init_l_Lean_Server_ServerTask_waitAny___auto__1();
    leanh::lean_mark_persistent(l_Lean_Server_ServerTask_waitAny___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_ServerTask(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Task(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_ServerTask(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_ServerTask(builtin);
}