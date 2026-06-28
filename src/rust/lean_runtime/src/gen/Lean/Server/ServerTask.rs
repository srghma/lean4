// Lean compiler output
// Module: Lean.Server.ServerTask
// Imports: Init.Task Init.System.IO
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::Task::{initialize_Init_Task, runtime_initialize_Init_Task};
use crate::lean_imports_rs::Init::Core::{
    lean_task_bind, lean_task_get_own, lean_task_map, lean_task_pure,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_utf8_byte_size,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_as_task, lean_io_bind_task, lean_io_cancel, lean_io_get_task_state, lean_io_map_task,
    lean_io_wait, lean_io_wait_any,
};
pub static l_Lean_Server_instCoeTaskServerTask___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Server_instCoeTaskServerTask___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instCoeTaskServerTask___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instCoeTaskServerTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_join___redArg___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_ServerTask_join___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_join___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_ServerTask_join___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_ServerTask_join___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__15_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__20_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__21_value)
            as *mut crate::leanh::LeanObject,
        3679434288154086795 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__25_value)
            as *mut crate::leanh::LeanObject,
        3984140175429830279 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_ServerTask_waitAny___auto__1___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Server_ServerTask_waitAny___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Server_instInhabitedServerTask_default___redArg(
    mut v_inst_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = lean_task_pure(v_inst_801_);
    return v___x_802_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerTask_default(
    mut v_00_u03b1_803_: *mut crate::leanh::LeanObject,
    mut v_inst_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = lean_task_pure(v_inst_804_);
    return v___x_805_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerTask___redArg(
    mut v_inst_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = lean_task_pure(v_inst_806_);
    return v___x_807_;
}
pub unsafe fn l_Lean_Server_instInhabitedServerTask(
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_inst_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = lean_task_pure(v_inst_809_);
    return v___x_810_;
}
pub unsafe fn l_Lean_Server_instCoeTaskServerTask___lam__0(
    mut v_task_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_task_811_);
    return v_task_811_;
}
pub unsafe fn l_Lean_Server_instCoeTaskServerTask___lam__0___boxed(
    mut v_task_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_Server_instCoeTaskServerTask___lam__0(v_task_812_);
    crate::leanh::lean_dec_ref(v_task_812_);
    return v_res_813_;
}
pub unsafe fn l_Lean_Server_instCoeTaskServerTask(
    mut v_00_u03b1_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_816_ = l_Lean_Server_instCoeTaskServerTask___closed__0;
    return v___f_816_;
}
pub unsafe fn l_Lean_Server_ServerTask_pure___redArg(
    mut v_x_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = lean_task_pure(v_x_817_);
    return v___x_818_;
}
pub unsafe fn l_Lean_Server_ServerTask_pure(
    mut v_00_u03b1_819_: *mut crate::leanh::LeanObject,
    mut v_x_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = lean_task_pure(v_x_820_);
    return v___x_821_;
}
pub unsafe fn l_Lean_Server_ServerTask_get___redArg(
    mut v_t_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = lean_task_get_own(v_t_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Server_ServerTask_get(
    mut v_00_u03b1_824_: *mut crate::leanh::LeanObject,
    mut v_t_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = lean_task_get_own(v_t_825_);
    return v___x_826_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait___redArg(
    mut v_t_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = lean_io_wait(v_t_827_);
    return v___x_829_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait___redArg___boxed(
    mut v_t_830_: *mut crate::leanh::LeanObject,
    mut v_a_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lean_Server_ServerTask_wait___redArg(v_t_830_);
    return v_res_832_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait(
    mut v_00_u03b1_833_: *mut crate::leanh::LeanObject,
    mut v_t_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = lean_io_wait(v_t_834_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Server_ServerTask_wait___boxed(
    mut v_00_u03b1_837_: *mut crate::leanh::LeanObject,
    mut v_t_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Lean_Server_ServerTask_wait(v_00_u03b1_837_, v_t_838_);
    return v_res_840_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCheap___redArg(
    mut v_f_841_: *mut crate::leanh::LeanObject,
    mut v_t_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_844_ = 1;
    v___x_845_ = lean_task_map(v_f_841_, v_t_842_, v___x_843_, v___x_844_);
    return v___x_845_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCheap(
    mut v_00_u03b1_846_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_847_: *mut crate::leanh::LeanObject,
    mut v_f_848_: *mut crate::leanh::LeanObject,
    mut v_t_849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = l_Lean_Server_ServerTask_mapCheap___redArg(v_f_848_, v_t_849_);
    return v___x_850_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCostly___redArg(
    mut v_f_851_: *mut crate::leanh::LeanObject,
    mut v_t_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: u8 = 0;
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_854_ = 0;
    v___x_855_ = lean_task_map(v_f_851_, v_t_852_, v___x_853_, v___x_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Server_ServerTask_mapCostly(
    mut v_00_u03b1_856_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_857_: *mut crate::leanh::LeanObject,
    mut v_f_858_: *mut crate::leanh::LeanObject,
    mut v_t_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_Server_ServerTask_mapCostly___redArg(v_f_858_, v_t_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCheap___redArg___lam__0(
    mut v_f_861_: *mut crate::leanh::LeanObject,
    mut v_x_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = crate::leanh::lean_apply_1(v_f_861_, v_x_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCheap___redArg(
    mut v_t_864_: *mut crate::leanh::LeanObject,
    mut v_f_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_866_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_bindCheap___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_866_, 0, v_f_865_);
    v___x_867_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_868_ = 1;
    v___x_869_ = lean_task_bind(v_t_864_, v___f_866_, v___x_867_, v___x_868_);
    return v___x_869_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCheap(
    mut v_00_u03b1_870_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_871_: *mut crate::leanh::LeanObject,
    mut v_t_872_: *mut crate::leanh::LeanObject,
    mut v_f_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_t_872_, v_f_873_);
    return v___x_874_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCostly___redArg(
    mut v_t_875_: *mut crate::leanh::LeanObject,
    mut v_f_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_877_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_bindCheap___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_877_, 0, v_f_876_);
    v___x_878_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_879_ = 0;
    v___x_880_ = lean_task_bind(v_t_875_, v___f_877_, v___x_878_, v___x_879_);
    return v___x_880_;
}
pub unsafe fn l_Lean_Server_ServerTask_bindCostly(
    mut v_00_u03b1_881_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_882_: *mut crate::leanh::LeanObject,
    mut v_t_883_: *mut crate::leanh::LeanObject,
    mut v_f_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lean_Server_ServerTask_bindCostly___redArg(v_t_883_, v_f_884_);
    return v___x_885_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0(
    mut v_acc_886_: *mut crate::leanh::LeanObject,
    mut v_x_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = lean_array_push(v_acc_886_, v_x_887_);
    return v___x_888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1(
    mut v_a_889_: *mut crate::leanh::LeanObject,
    mut v_acc_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_891_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_891_, 0, v_acc_890_);
    v___x_892_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_891_, v_a_889_);
    return v___x_892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(
    mut v_as_893_: *mut crate::leanh::LeanObject,
    mut v_sz_894_: usize,
    mut v_i_895_: usize,
    mut v_b_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_897_: u8 = 0;
    let mut v_a_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_inc(v_a_898_);
                    v___f_899_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg___lam__1 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_899_, 0, v_a_898_);
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
    mut v_as_904_: *mut crate::leanh::LeanObject,
    mut v_sz_905_: *mut crate::leanh::LeanObject,
    mut v_i_906_: *mut crate::leanh::LeanObject,
    mut v_b_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_908_: usize = 0;
    let mut v_i_boxed_909_: usize = 0;
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_908_ = crate::leanh::lean_unbox_usize(v_sz_905_);
    crate::leanh::lean_dec(v_sz_905_);
    v_i_boxed_909_ = crate::leanh::lean_unbox_usize(v_i_906_);
    crate::leanh::lean_dec(v_i_906_);
    v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_904_, v_sz_boxed_908_, v_i_boxed_909_, v_b_907_);
    crate::leanh::lean_dec_ref(v_as_904_);
    return v_res_910_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_join___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_Server_ServerTask_join___redArg___closed__0;
    v_r_914_ = lean_task_pure(v___x_913_);
    return v_r_914_;
}
pub unsafe fn l_Lean_Server_ServerTask_join___redArg(
    mut v_ts_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_917_: usize = 0;
    let mut v___x_918_: usize = 0;
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_916_ = crate::leanh::lean_obj_once(
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
    mut v_ts_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Lean_Server_ServerTask_join___redArg(v_ts_920_);
    crate::leanh::lean_dec_ref(v_ts_920_);
    return v_res_921_;
}
pub unsafe fn l_Lean_Server_ServerTask_join(
    mut v_00_u03b1_922_: *mut crate::leanh::LeanObject,
    mut v_ts_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Lean_Server_ServerTask_join___redArg(v_ts_923_);
    return v___x_924_;
}
pub unsafe fn l_Lean_Server_ServerTask_join___boxed(
    mut v_00_u03b1_925_: *mut crate::leanh::LeanObject,
    mut v_ts_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ = l_Lean_Server_ServerTask_join(v_00_u03b1_925_, v_ts_926_);
    crate::leanh::lean_dec_ref(v_ts_926_);
    return v_res_927_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(
    mut v_00_u03b1_928_: *mut crate::leanh::LeanObject,
    mut v_as_929_: *mut crate::leanh::LeanObject,
    mut v_sz_930_: usize,
    mut v_i_931_: usize,
    mut v_b_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___redArg(v_as_929_, v_sz_930_, v_i_931_, v_b_932_);
    return v___x_933_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0___boxed(
    mut v_00_u03b1_934_: *mut crate::leanh::LeanObject,
    mut v_as_935_: *mut crate::leanh::LeanObject,
    mut v_sz_936_: *mut crate::leanh::LeanObject,
    mut v_i_937_: *mut crate::leanh::LeanObject,
    mut v_b_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_939_: usize = 0;
    let mut v_i_boxed_940_: usize = 0;
    let mut v_res_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_939_ = crate::leanh::lean_unbox_usize(v_sz_936_);
    crate::leanh::lean_dec(v_sz_936_);
    v_i_boxed_940_ = crate::leanh::lean_unbox_usize(v_i_937_);
    crate::leanh::lean_dec(v_i_937_);
    v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_ServerTask_join_spec__0(v_00_u03b1_934_, v_as_935_, v_sz_boxed_939_, v_i_boxed_940_, v_b_938_);
    crate::leanh::lean_dec_ref(v_as_935_);
    return v_res_941_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask___redArg(
    mut v_act_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_945_ = lean_io_as_task(v_act_942_, v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask___redArg___boxed(
    mut v_act_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_946_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask(
    mut v_00_u03b1_949_: *mut crate::leanh::LeanObject,
    mut v_act_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v_act_950_);
    return v___x_952_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_asTask___boxed(
    mut v_00_u03b1_953_: *mut crate::leanh::LeanObject,
    mut v_act_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_Server_ServerTask_BaseIO_asTask(v_00_u03b1_953_, v_act_954_);
    return v_res_956_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(
    mut v_f_957_: *mut crate::leanh::LeanObject,
    mut v_t_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u8 = 0;
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_961_ = 1;
    v___x_962_ = lean_io_map_task(v_f_957_, v_t_958_, v___x_960_, v___x_961_);
    return v___x_962_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg___boxed(
    mut v_f_963_: *mut crate::leanh::LeanObject,
    mut v_t_964_: *mut crate::leanh::LeanObject,
    mut v_a_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_963_, v_t_964_);
    return v_res_966_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(
    mut v_00_u03b1_967_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_968_: *mut crate::leanh::LeanObject,
    mut v_f_969_: *mut crate::leanh::LeanObject,
    mut v_t_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___redArg(v_f_969_, v_t_970_);
    return v___x_972_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCheap___boxed(
    mut v_00_u03b1_973_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_974_: *mut crate::leanh::LeanObject,
    mut v_f_975_: *mut crate::leanh::LeanObject,
    mut v_t_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCheap(
        v_00_u03b1_973_,
        v_00_u03b2_974_,
        v_f_975_,
        v_t_976_,
    );
    return v_res_978_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(
    mut v_f_979_: *mut crate::leanh::LeanObject,
    mut v_t_980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_983_ = 0;
    v___x_984_ = lean_io_map_task(v_f_979_, v_t_980_, v___x_982_, v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg___boxed(
    mut v_f_985_: *mut crate::leanh::LeanObject,
    mut v_t_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_985_, v_t_986_);
    return v_res_988_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(
    mut v_00_u03b1_989_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_990_: *mut crate::leanh::LeanObject,
    mut v_f_991_: *mut crate::leanh::LeanObject,
    mut v_t_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___redArg(v_f_991_, v_t_992_);
    return v___x_994_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_mapTaskCostly___boxed(
    mut v_00_u03b1_995_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_996_: *mut crate::leanh::LeanObject,
    mut v_f_997_: *mut crate::leanh::LeanObject,
    mut v_t_998_: *mut crate::leanh::LeanObject,
    mut v_a_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lean_Server_ServerTask_BaseIO_mapTaskCostly(
        v_00_u03b1_995_,
        v_00_u03b2_996_,
        v_f_997_,
        v_t_998_,
    );
    return v_res_1000_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(
    mut v_f_1001_: *mut crate::leanh::LeanObject,
    mut v_x_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = crate::leanh::lean_apply_2(v_f_1001_, v_x_1002_, crate::leanh::lean_box(0));
    return v___x_1004_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed(
    mut v_f_1005_: *mut crate::leanh::LeanObject,
    mut v_x_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1008_ =
        l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0(v_f_1005_, v_x_1006_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(
    mut v_t_1009_: *mut crate::leanh::LeanObject,
    mut v_f_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1012_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1012_, 0, v_f_1010_);
    v___x_1013_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1014_ = 1;
    v___x_1015_ = lean_io_bind_task(v_t_1009_, v___f_1012_, v___x_1013_, v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___boxed(
    mut v_t_1016_: *mut crate::leanh::LeanObject,
    mut v_f_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_1016_, v_f_1017_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(
    mut v_00_u03b1_1020_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1021_: *mut crate::leanh::LeanObject,
    mut v_t_1022_: *mut crate::leanh::LeanObject,
    mut v_f_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg(v_t_1022_, v_f_1023_);
    return v___x_1025_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___boxed(
    mut v_00_u03b1_1026_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1027_: *mut crate::leanh::LeanObject,
    mut v_t_1028_: *mut crate::leanh::LeanObject,
    mut v_f_1029_: *mut crate::leanh::LeanObject,
    mut v_a_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCheap(
        v_00_u03b1_1026_,
        v_00_u03b2_1027_,
        v_t_1028_,
        v_f_1029_,
    );
    return v_res_1031_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(
    mut v_t_1032_: *mut crate::leanh::LeanObject,
    mut v_f_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1035_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_BaseIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1035_, 0, v_f_1033_);
    v___x_1036_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1037_ = 0;
    v___x_1038_ = lean_io_bind_task(v_t_1032_, v___f_1035_, v___x_1036_, v___x_1037_);
    return v___x_1038_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg___boxed(
    mut v_t_1039_: *mut crate::leanh::LeanObject,
    mut v_f_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_1039_, v_f_1040_);
    return v_res_1042_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(
    mut v_00_u03b1_1043_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1044_: *mut crate::leanh::LeanObject,
    mut v_t_1045_: *mut crate::leanh::LeanObject,
    mut v_f_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___redArg(v_t_1045_, v_f_1046_);
    return v___x_1048_;
}
pub unsafe fn l_Lean_Server_ServerTask_BaseIO_bindTaskCostly___boxed(
    mut v_00_u03b1_1049_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1050_: *mut crate::leanh::LeanObject,
    mut v_t_1051_: *mut crate::leanh::LeanObject,
    mut v_f_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_Server_ServerTask_BaseIO_bindTaskCostly(
        v_00_u03b1_1049_,
        v_00_u03b2_1050_,
        v_t_1051_,
        v_f_1052_,
    );
    return v_res_1054_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(
    mut v_act_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1061_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1065_: u8 = 0;
    let mut v_a_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1069_: u8 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1057_ = crate::leanh::lean_apply_1(v_act_1055_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1057_) == 0 {
                    v_a_1058_ = crate::leanh::lean_ctor_get(v___x_1057_, 0);
                    v_isSharedCheck_1065_ = (!crate::leanh::lean_is_exclusive(v___x_1057_)) as u8;
                    if v_isSharedCheck_1065_ == 0 {
                        v___x_1060_ = v___x_1057_;
                        v_isShared_1061_ = v_isSharedCheck_1065_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1058_);
                        crate::leanh::lean_dec(v___x_1057_);
                        v___x_1060_ = crate::leanh::lean_box(0);
                        v_isShared_1061_ = v_isSharedCheck_1065_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1066_ = crate::leanh::lean_ctor_get(v___x_1057_, 0);
                    v_isSharedCheck_1073_ = (!crate::leanh::lean_is_exclusive(v___x_1057_)) as u8;
                    if v_isSharedCheck_1073_ == 0 {
                        v___x_1068_ = v___x_1057_;
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1066_);
                        crate::leanh::lean_dec(v___x_1057_);
                        v___x_1068_ = crate::leanh::lean_box(0);
                        v_isShared_1069_ = v_isSharedCheck_1073_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1061_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1060_, 1);
                    v___x_1063_ = v___x_1060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1068_, 0);
                    v___x_1071_ = v___x_1068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
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
    mut v_act_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1076_ = l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0(v_act_1074_);
    return v_res_1076_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg(
    mut v_act_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1079_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1079_, 0, v_act_1077_);
    v___x_1080_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1081_ = lean_io_as_task(v___f_1079_, v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___redArg___boxed(
    mut v_act_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_1082_);
    return v_res_1084_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask(
    mut v_00_u03b5_1085_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1086_: *mut crate::leanh::LeanObject,
    mut v_act_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_Server_ServerTask_EIO_asTask___redArg(v_act_1087_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_asTask___boxed(
    mut v_00_u03b5_1090_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1091_: *mut crate::leanh::LeanObject,
    mut v_act_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1094_ =
        l_Lean_Server_ServerTask_EIO_asTask(v_00_u03b5_1090_, v_00_u03b1_1091_, v_act_1092_);
    return v_res_1094_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(
    mut v_f_1095_: *mut crate::leanh::LeanObject,
    mut v_a_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut v_a_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1098_ =
                    crate::leanh::lean_apply_2(v_f_1095_, v_a_1096_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1098_) == 0 {
                    v_a_1099_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1106_ = (!crate::leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1106_ == 0 {
                        v___x_1101_ = v___x_1098_;
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1099_);
                        crate::leanh::lean_dec(v___x_1098_);
                        v___x_1101_ = crate::leanh::lean_box(0);
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1107_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1114_ = (!crate::leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1114_ == 0 {
                        v___x_1109_ = v___x_1098_;
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1107_);
                        crate::leanh::lean_dec(v___x_1098_);
                        v___x_1109_ = crate::leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1114_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1102_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1101_, 1);
                    v___x_1104_ = v___x_1101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1109_, 0);
                    v___x_1112_ = v___x_1109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
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
    mut v_f_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0(v_f_1115_, v_a_1116_);
    return v_res_1118_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(
    mut v_f_1119_: *mut crate::leanh::LeanObject,
    mut v_t_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1122_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1122_, 0, v_f_1119_);
    v___x_1123_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1124_ = 1;
    v___x_1125_ = lean_io_map_task(v___f_1122_, v_t_1120_, v___x_1123_, v___x_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___boxed(
    mut v_f_1126_: *mut crate::leanh::LeanObject,
    mut v_t_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_1126_, v_t_1127_);
    return v_res_1129_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap(
    mut v_00_u03b1_1130_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1131_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1132_: *mut crate::leanh::LeanObject,
    mut v_f_1133_: *mut crate::leanh::LeanObject,
    mut v_t_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg(v_f_1133_, v_t_1134_);
    return v___x_1136_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCheap___boxed(
    mut v_00_u03b1_1137_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1139_: *mut crate::leanh::LeanObject,
    mut v_f_1140_: *mut crate::leanh::LeanObject,
    mut v_t_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_1144_: *mut crate::leanh::LeanObject,
    mut v_t_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1147_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1147_, 0, v_f_1144_);
    v___x_1148_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1149_ = 0;
    v___x_1150_ = lean_io_map_task(v___f_1147_, v_t_1145_, v___x_1148_, v___x_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg___boxed(
    mut v_f_1151_: *mut crate::leanh::LeanObject,
    mut v_t_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_1151_, v_t_1152_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly(
    mut v_00_u03b1_1155_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1156_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1157_: *mut crate::leanh::LeanObject,
    mut v_f_1158_: *mut crate::leanh::LeanObject,
    mut v_t_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Server_ServerTask_EIO_mapTaskCostly___redArg(v_f_1158_, v_t_1159_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_mapTaskCostly___boxed(
    mut v_00_u03b1_1162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1164_: *mut crate::leanh::LeanObject,
    mut v_f_1165_: *mut crate::leanh::LeanObject,
    mut v_t_1166_: *mut crate::leanh::LeanObject,
    mut v_a_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_f_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1172_ =
                    crate::leanh::lean_apply_2(v_f_1169_, v_a_1170_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1172_) == 0 {
                    v_a_1173_ = crate::leanh::lean_ctor_get(v___x_1172_, 0);
                    crate::leanh::lean_inc(v_a_1173_);
                    crate::leanh::lean_dec_ref_known(v___x_1172_, 1);
                    return v_a_1173_;
                } else {
                    v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1172_, 0);
                    v_isSharedCheck_1182_ = (!crate::leanh::lean_is_exclusive(v___x_1172_)) as u8;
                    if v_isSharedCheck_1182_ == 0 {
                        v___x_1176_ = v___x_1172_;
                        v_isShared_1177_ = v_isSharedCheck_1182_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1174_);
                        crate::leanh::lean_dec(v___x_1172_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1182_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1176_, 0);
                    v___x_1179_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1174_);
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
    mut v_f_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0(v_f_1183_, v_a_1184_);
    return v_res_1186_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(
    mut v_t_1187_: *mut crate::leanh::LeanObject,
    mut v_f_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1190_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1190_, 0, v_f_1188_);
    v___x_1191_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1192_ = 1;
    v___x_1193_ = lean_io_bind_task(v_t_1187_, v___f_1190_, v___x_1191_, v___x_1192_);
    return v___x_1193_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___boxed(
    mut v_t_1194_: *mut crate::leanh::LeanObject,
    mut v_f_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_1194_, v_f_1195_);
    return v_res_1197_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap(
    mut v_00_u03b1_1198_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1199_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1200_: *mut crate::leanh::LeanObject,
    mut v_t_1201_: *mut crate::leanh::LeanObject,
    mut v_f_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg(v_t_1201_, v_f_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCheap___boxed(
    mut v_00_u03b1_1205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1206_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1207_: *mut crate::leanh::LeanObject,
    mut v_t_1208_: *mut crate::leanh::LeanObject,
    mut v_f_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_t_1212_: *mut crate::leanh::LeanObject,
    mut v_f_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1215_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_EIO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1215_, 0, v_f_1213_);
    v___x_1216_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1217_ = 0;
    v___x_1218_ = lean_io_bind_task(v_t_1212_, v___f_1215_, v___x_1216_, v___x_1217_);
    return v___x_1218_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg___boxed(
    mut v_t_1219_: *mut crate::leanh::LeanObject,
    mut v_f_1220_: *mut crate::leanh::LeanObject,
    mut v_a_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_1219_, v_f_1220_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly(
    mut v_00_u03b1_1223_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1224_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1225_: *mut crate::leanh::LeanObject,
    mut v_t_1226_: *mut crate::leanh::LeanObject,
    mut v_f_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lean_Server_ServerTask_EIO_bindTaskCostly___redArg(v_t_1226_, v_f_1227_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_Server_ServerTask_EIO_bindTaskCostly___boxed(
    mut v_00_u03b1_1230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1232_: *mut crate::leanh::LeanObject,
    mut v_t_1233_: *mut crate::leanh::LeanObject,
    mut v_f_1234_: *mut crate::leanh::LeanObject,
    mut v_a_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_act_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_a_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1239_ = crate::leanh::lean_apply_1(v_act_1237_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1239_) == 0 {
                    v_a_1240_ = crate::leanh::lean_ctor_get(v___x_1239_, 0);
                    v_isSharedCheck_1247_ = (!crate::leanh::lean_is_exclusive(v___x_1239_)) as u8;
                    if v_isSharedCheck_1247_ == 0 {
                        v___x_1242_ = v___x_1239_;
                        v_isShared_1243_ = v_isSharedCheck_1247_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1240_);
                        crate::leanh::lean_dec(v___x_1239_);
                        v___x_1242_ = crate::leanh::lean_box(0);
                        v_isShared_1243_ = v_isSharedCheck_1247_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1248_ = crate::leanh::lean_ctor_get(v___x_1239_, 0);
                    v_isSharedCheck_1255_ = (!crate::leanh::lean_is_exclusive(v___x_1239_)) as u8;
                    if v_isSharedCheck_1255_ == 0 {
                        v___x_1250_ = v___x_1239_;
                        v_isShared_1251_ = v_isSharedCheck_1255_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1248_);
                        crate::leanh::lean_dec(v___x_1239_);
                        v___x_1250_ = crate::leanh::lean_box(0);
                        v_isShared_1251_ = v_isSharedCheck_1255_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1243_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1242_, 1);
                    v___x_1245_ = v___x_1242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1250_, 0);
                    v___x_1253_ = v___x_1250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
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
    mut v_act_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0(v_act_1256_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___redArg(
    mut v_act_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1261_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_asTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1261_, 0, v_act_1259_);
    v___x_1262_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1263_ = lean_io_as_task(v___f_1261_, v___x_1262_);
    return v___x_1263_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___redArg___boxed(
    mut v_act_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_1264_);
    return v_res_1266_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask(
    mut v_00_u03b1_1267_: *mut crate::leanh::LeanObject,
    mut v_act_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1270_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v_act_1268_);
    return v___x_1270_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_asTask___boxed(
    mut v_00_u03b1_1271_: *mut crate::leanh::LeanObject,
    mut v_act_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lean_Server_ServerTask_IO_asTask(v_00_u03b1_1271_, v_act_1272_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(
    mut v_f_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v_a_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1278_ =
                    crate::leanh::lean_apply_2(v_f_1275_, v_a_1276_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1278_) == 0 {
                    v_a_1279_ = crate::leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1286_ = (!crate::leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___x_1278_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1279_);
                        crate::leanh::lean_dec(v___x_1278_);
                        v___x_1281_ = crate::leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1287_ = crate::leanh::lean_ctor_get(v___x_1278_, 0);
                    v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v___x_1278_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1289_ = v___x_1278_;
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1287_);
                        crate::leanh::lean_dec(v___x_1278_);
                        v___x_1289_ = crate::leanh::lean_box(0);
                        v_isShared_1290_ = v_isSharedCheck_1294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1282_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1281_, 1);
                    v___x_1284_ = v___x_1281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1289_, 0);
                    v___x_1292_ = v___x_1289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
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
    mut v_f_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0(v_f_1295_, v_a_1296_);
    return v_res_1298_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(
    mut v_f_1299_: *mut crate::leanh::LeanObject,
    mut v_t_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: u8 = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1302_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1302_, 0, v_f_1299_);
    v___x_1303_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1304_ = 1;
    v___x_1305_ = lean_io_map_task(v___f_1302_, v_t_1300_, v___x_1303_, v___x_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___boxed(
    mut v_f_1306_: *mut crate::leanh::LeanObject,
    mut v_t_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1309_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_1306_, v_t_1307_);
    return v_res_1309_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap(
    mut v_00_u03b1_1310_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1311_: *mut crate::leanh::LeanObject,
    mut v_f_1312_: *mut crate::leanh::LeanObject,
    mut v_t_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg(v_f_1312_, v_t_1313_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCheap___boxed(
    mut v_00_u03b1_1316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1317_: *mut crate::leanh::LeanObject,
    mut v_f_1318_: *mut crate::leanh::LeanObject,
    mut v_t_1319_: *mut crate::leanh::LeanObject,
    mut v_a_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Lean_Server_ServerTask_IO_mapTaskCheap(
        v_00_u03b1_1316_,
        v_00_u03b2_1317_,
        v_f_1318_,
        v_t_1319_,
    );
    return v_res_1321_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(
    mut v_f_1322_: *mut crate::leanh::LeanObject,
    mut v_t_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1325_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_mapTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1325_, 0, v_f_1322_);
    v___x_1326_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1327_ = 0;
    v___x_1328_ = lean_io_map_task(v___f_1325_, v_t_1323_, v___x_1326_, v___x_1327_);
    return v___x_1328_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg___boxed(
    mut v_f_1329_: *mut crate::leanh::LeanObject,
    mut v_t_1330_: *mut crate::leanh::LeanObject,
    mut v_a_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_1329_, v_t_1330_);
    return v_res_1332_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly(
    mut v_00_u03b1_1333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1334_: *mut crate::leanh::LeanObject,
    mut v_f_1335_: *mut crate::leanh::LeanObject,
    mut v_t_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = l_Lean_Server_ServerTask_IO_mapTaskCostly___redArg(v_f_1335_, v_t_1336_);
    return v___x_1338_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_mapTaskCostly___boxed(
    mut v_00_u03b1_1339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1340_: *mut crate::leanh::LeanObject,
    mut v_f_1341_: *mut crate::leanh::LeanObject,
    mut v_t_1342_: *mut crate::leanh::LeanObject,
    mut v_a_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Lean_Server_ServerTask_IO_mapTaskCostly(
        v_00_u03b1_1339_,
        v_00_u03b2_1340_,
        v_f_1341_,
        v_t_1342_,
    );
    return v_res_1344_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(
    mut v_f_1345_: *mut crate::leanh::LeanObject,
    mut v_a_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1348_ =
                    crate::leanh::lean_apply_2(v_f_1345_, v_a_1346_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_1348_) == 0 {
                    v_a_1349_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                    crate::leanh::lean_inc(v_a_1349_);
                    crate::leanh::lean_dec_ref_known(v___x_1348_, 1);
                    return v_a_1349_;
                } else {
                    v_a_1350_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1358_ = (!crate::leanh::lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1358_ == 0 {
                        v___x_1352_ = v___x_1348_;
                        v_isShared_1353_ = v_isSharedCheck_1358_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1350_);
                        crate::leanh::lean_dec(v___x_1348_);
                        v___x_1352_ = crate::leanh::lean_box(0);
                        v_isShared_1353_ = v_isSharedCheck_1358_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1353_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1352_, 0);
                    v___x_1355_ = v___x_1352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1350_);
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
    mut v_f_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0(v_f_1359_, v_a_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(
    mut v_t_1363_: *mut crate::leanh::LeanObject,
    mut v_f_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1366_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1366_, 0, v_f_1364_);
    v___x_1367_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1368_ = 1;
    v___x_1369_ = lean_io_bind_task(v_t_1363_, v___f_1366_, v___x_1367_, v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___boxed(
    mut v_t_1370_: *mut crate::leanh::LeanObject,
    mut v_f_1371_: *mut crate::leanh::LeanObject,
    mut v_a_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_1370_, v_f_1371_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap(
    mut v_00_u03b1_1374_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1375_: *mut crate::leanh::LeanObject,
    mut v_t_1376_: *mut crate::leanh::LeanObject,
    mut v_f_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg(v_t_1376_, v_f_1377_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCheap___boxed(
    mut v_00_u03b1_1380_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1381_: *mut crate::leanh::LeanObject,
    mut v_t_1382_: *mut crate::leanh::LeanObject,
    mut v_f_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l_Lean_Server_ServerTask_IO_bindTaskCheap(
        v_00_u03b1_1380_,
        v_00_u03b2_1381_,
        v_t_1382_,
        v_f_1383_,
    );
    return v_res_1385_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(
    mut v_t_1386_: *mut crate::leanh::LeanObject,
    mut v_f_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1389_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_ServerTask_IO_bindTaskCheap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1389_, 0, v_f_1387_);
    v___x_1390_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1391_ = 0;
    v___x_1392_ = lean_io_bind_task(v_t_1386_, v___f_1389_, v___x_1390_, v___x_1391_);
    return v___x_1392_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg___boxed(
    mut v_t_1393_: *mut crate::leanh::LeanObject,
    mut v_f_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_1393_, v_f_1394_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly(
    mut v_00_u03b1_1397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1398_: *mut crate::leanh::LeanObject,
    mut v_t_1399_: *mut crate::leanh::LeanObject,
    mut v_f_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Lean_Server_ServerTask_IO_bindTaskCostly___redArg(v_t_1399_, v_f_1400_);
    return v___x_1402_;
}
pub unsafe fn l_Lean_Server_ServerTask_IO_bindTaskCostly___boxed(
    mut v_00_u03b1_1403_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1404_: *mut crate::leanh::LeanObject,
    mut v_t_1405_: *mut crate::leanh::LeanObject,
    mut v_f_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_Server_ServerTask_IO_bindTaskCostly(
        v_00_u03b1_1403_,
        v_00_u03b2_1404_,
        v_t_1405_,
        v_f_1406_,
    );
    return v_res_1408_;
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished___redArg(
    mut v_t_1409_: *mut crate::leanh::LeanObject,
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
    mut v_t_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1416_: u8 = 0;
    let mut v_r_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_1414_);
    crate::leanh::lean_dec_ref(v_t_1414_);
    v_r_1417_ = crate::leanh::lean_box((v_res_1416_) as usize);
    return v_r_1417_;
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished(
    mut v_00_u03b1_1418_: *mut crate::leanh::LeanObject,
    mut v_t_1419_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1421_: u8 = 0;
    v___x_1421_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_t_1419_);
    return v___x_1421_;
}
pub unsafe fn l_Lean_Server_ServerTask_hasFinished___boxed(
    mut v_00_u03b1_1422_: *mut crate::leanh::LeanObject,
    mut v_t_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: u8 = 0;
    let mut v_r_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_Lean_Server_ServerTask_hasFinished(v_00_u03b1_1422_, v_t_1423_);
    crate::leanh::lean_dec_ref(v_t_1423_);
    v_r_1426_ = crate::leanh::lean_box((v_res_1425_) as usize);
    return v_r_1426_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__10;
    v___x_1454_ = l_Lean_mkAtom(v___x_1453_);
    return v___x_1454_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__12_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__12,
    );
    v___x_1456_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1457_ = lean_array_push(v___x_1456_, v___x_1455_);
    return v___x_1457_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1466_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__17;
    v___x_1467_ = lean_string_utf8_byte_size(v___x_1466_);
    return v___x_1467_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__18_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__18,
    );
    v___x_1469_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1470_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__17;
    v___x_1471_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1470_);
    crate::leanh::lean_ctor_set(v___x_1471_, 1, v___x_1469_);
    crate::leanh::lean_ctor_set(v___x_1471_, 2, v___x_1468_);
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = crate::leanh::lean_box(0);
    v___x_1478_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__22;
    v___x_1479_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__19_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__19,
    );
    v___x_1480_ = crate::leanh::lean_box(2);
    v___x_1481_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1481_, 0, v___x_1480_);
    crate::leanh::lean_ctor_set(v___x_1481_, 1, v___x_1479_);
    crate::leanh::lean_ctor_set(v___x_1481_, 2, v___x_1478_);
    crate::leanh::lean_ctor_set(v___x_1481_, 3, v___x_1477_);
    return v___x_1481_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1482_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__23_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__23,
    );
    v___x_1483_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1484_ = lean_array_push(v___x_1483_, v___x_1482_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__27;
    v___x_1493_ = l_Lean_mkAtom(v___x_1492_);
    return v___x_1493_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__28_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__28,
    );
    v___x_1495_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1496_ = lean_array_push(v___x_1495_, v___x_1494_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__29_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__29,
    );
    v___x_1498_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__26;
    v___x_1499_ = crate::leanh::lean_box(2);
    v___x_1500_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1499_);
    crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1498_);
    crate::leanh::lean_ctor_set(v___x_1500_, 2, v___x_1497_);
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__30_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__30,
    );
    v___x_1502_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1503_ = lean_array_push(v___x_1502_, v___x_1501_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__31_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__31,
    );
    v___x_1505_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__9;
    v___x_1506_ = crate::leanh::lean_box(2);
    v___x_1507_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1505_);
    crate::leanh::lean_ctor_set(v___x_1507_, 2, v___x_1504_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__32_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__32,
    );
    v___x_1509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__24_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__24,
    );
    v___x_1510_ = lean_array_push(v___x_1509_, v___x_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__33_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__33,
    );
    v___x_1512_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__16;
    v___x_1513_ = crate::leanh::lean_box(2);
    v___x_1514_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    crate::leanh::lean_ctor_set(v___x_1514_, 1, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1514_, 2, v___x_1511_);
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__34_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__34,
    );
    v___x_1516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__13_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__13,
    );
    v___x_1517_ = lean_array_push(v___x_1516_, v___x_1515_);
    return v___x_1517_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__35_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__35,
    );
    v___x_1519_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__11;
    v___x_1520_ = crate::leanh::lean_box(2);
    v___x_1521_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1521_, 0, v___x_1520_);
    crate::leanh::lean_ctor_set(v___x_1521_, 1, v___x_1519_);
    crate::leanh::lean_ctor_set(v___x_1521_, 2, v___x_1518_);
    return v___x_1521_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__36_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__36,
    );
    v___x_1523_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1524_ = lean_array_push(v___x_1523_, v___x_1522_);
    return v___x_1524_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__37_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__37,
    );
    v___x_1526_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__9;
    v___x_1527_ = crate::leanh::lean_box(2);
    v___x_1528_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1527_);
    crate::leanh::lean_ctor_set(v___x_1528_, 1, v___x_1526_);
    crate::leanh::lean_ctor_set(v___x_1528_, 2, v___x_1525_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__38_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__38,
    );
    v___x_1530_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1531_ = lean_array_push(v___x_1530_, v___x_1529_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__39_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__39,
    );
    v___x_1533_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__7;
    v___x_1534_ = crate::leanh::lean_box(2);
    v___x_1535_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    crate::leanh::lean_ctor_set(v___x_1535_, 1, v___x_1533_);
    crate::leanh::lean_ctor_set(v___x_1535_, 2, v___x_1532_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__40_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__40,
    );
    v___x_1537_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__5;
    v___x_1538_ = lean_array_push(v___x_1537_, v___x_1536_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__41_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__41,
    );
    v___x_1540_ = l_Lean_Server_ServerTask_waitAny___auto__1___closed__4;
    v___x_1541_ = crate::leanh::lean_box(2);
    v___x_1542_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
    crate::leanh::lean_ctor_set(v___x_1542_, 1, v___x_1540_);
    crate::leanh::lean_ctor_set(v___x_1542_, 2, v___x_1539_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Lean_Server_ServerTask_waitAny___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Lean_Server_ServerTask_waitAny___auto__1___closed__42_once),
        _init_l_Lean_Server_ServerTask_waitAny___auto__1___closed__42,
    );
    return v___x_1543_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1544_) == 0 {
                    v___x_1546_ = l_List_reverse___redArg(v_a_1545_);
                    return v___x_1546_;
                } else {
                    v_head_1547_ = crate::leanh::lean_ctor_get(v_a_1544_, 0);
                    v_tail_1548_ = crate::leanh::lean_ctor_get(v_a_1544_, 1);
                    v_isSharedCheck_1556_ = (!crate::leanh::lean_is_exclusive(v_a_1544_)) as u8;
                    if v_isSharedCheck_1556_ == 0 {
                        v___x_1550_ = v_a_1544_;
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1548_);
                        crate::leanh::lean_inc(v_head_1547_);
                        crate::leanh::lean_dec(v_a_1544_);
                        v___x_1550_ = crate::leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1550_, 1, v_a_1545_);
                    v___x_1553_ = v___x_1550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_head_1547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_a_1545_);
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
    mut v_tasks_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = crate::leanh::lean_box(0);
    v___x_1560_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(
        v_tasks_1557_,
        v___x_1559_,
    );
    v___x_1561_ = lean_io_wait_any(v___x_1560_);
    crate::leanh::lean_dec(v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny___redArg___boxed(
    mut v_tasks_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1564_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_1562_);
    return v_res_1564_;
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny(
    mut v_00_u03b1_1565_: *mut crate::leanh::LeanObject,
    mut v_tasks_1566_: *mut crate::leanh::LeanObject,
    mut v_h_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_Lean_Server_ServerTask_waitAny___redArg(v_tasks_1566_);
    return v___x_1569_;
}
pub unsafe fn l_Lean_Server_ServerTask_waitAny___boxed(
    mut v_00_u03b1_1570_: *mut crate::leanh::LeanObject,
    mut v_tasks_1571_: *mut crate::leanh::LeanObject,
    mut v_h_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_Server_ServerTask_waitAny(v_00_u03b1_1570_, v_tasks_1571_, v_h_1572_);
    return v_res_1574_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0(
    mut v_00_u03b1_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1578_ = l_List_mapTR_loop___at___00Lean_Server_ServerTask_waitAny_spec__0___redArg(
        v_a_1576_, v_a_1577_,
    );
    return v___x_1578_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel___redArg(
    mut v_t_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = lean_io_cancel(v_t_1579_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel___redArg___boxed(
    mut v_t_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_Server_ServerTask_cancel___redArg(v_t_1582_);
    crate::leanh::lean_dec_ref(v_t_1582_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel(
    mut v_00_u03b1_1585_: *mut crate::leanh::LeanObject,
    mut v_t_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = lean_io_cancel(v_t_1586_);
    return v___x_1588_;
}
pub unsafe fn l_Lean_Server_ServerTask_cancel___boxed(
    mut v_00_u03b1_1589_: *mut crate::leanh::LeanObject,
    mut v_t_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_Lean_Server_ServerTask_cancel(v_00_u03b1_1589_, v_t_1590_);
    crate::leanh::lean_dec_ref(v_t_1590_);
    return v_res_1592_;
}
pub unsafe fn l_Task_asServerTask___redArg(
    mut v_t_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_t_1593_);
    return v_t_1593_;
}
pub unsafe fn l_Task_asServerTask___redArg___boxed(
    mut v_t_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ = l_Task_asServerTask___redArg(v_t_1594_);
    crate::leanh::lean_dec_ref(v_t_1594_);
    return v_res_1595_;
}
pub unsafe fn l_Task_asServerTask(
    mut v_00_u03b1_1596_: *mut crate::leanh::LeanObject,
    mut v_t_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_t_1597_);
    return v_t_1597_;
}
pub unsafe fn l_Task_asServerTask___boxed(
    mut v_00_u03b1_1598_: *mut crate::leanh::LeanObject,
    mut v_t_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Task_asServerTask(v_00_u03b1_1598_, v_t_1599_);
    crate::leanh::lean_dec_ref(v_t_1599_);
    return v_res_1600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_ServerTask(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_ServerTask(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Server_ServerTask_waitAny___auto__1 = _init_l_Lean_Server_ServerTask_waitAny___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_Server_ServerTask_waitAny___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_ServerTask(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_ServerTask(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_ServerTask(builtin);
}
