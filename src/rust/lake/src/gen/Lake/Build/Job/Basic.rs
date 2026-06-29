// Lean compiler output
// Module: Lake.Build.Job.Basic
// Imports: Lake.Util.Log Lake.Util.Task Lake.Util.Opaque Lake.Build.Trace Lake.Build.Data
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
use crate::r#gen::Lake::Build::Data::{
    initialize_Lake_Build_Data, l_Lake_instDataKindUnit, runtime_initialize_Lake_Build_Data,
};
use crate::r#gen::Lake::Build::Trace::{
    initialize_Lake_Build_Trace, l_Lake_BuildTrace_mix, l_Lake_BuildTrace_nil,
    runtime_initialize_Lake_Build_Trace,
};
use crate::r#gen::Lake::Util::Log::{initialize_Lake_Util_Log, runtime_initialize_Lake_Util_Log};
use crate::r#gen::Lake::Util::Opaque::{
    initialize_Lake_Util_Opaque, runtime_initialize_Lake_Util_Opaque,
};
use crate::r#gen::Lake::Util::Task::{
    initialize_Lake_Util_Task, runtime_initialize_Lake_Util_Task,
};
use crate::lean_imports_rs::Init::Core::{lean_task_get_own, lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_utf8_byte_size,
};
pub static mut l_Lake_instInhabitedJobAction_default: u8 = 0;
pub static mut l_Lake_instInhabitedJobAction: u8 = 0;
pub static l_Lake_instReprJobAction_repr___closed__0_value: crate::leanh::LeanStringObject<23> =
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
            76, 97, 107, 101, 46, 74, 111, 98, 65, 99, 116, 105, 111, 110, 46, 117, 110, 107, 110,
            111, 119, 110, 0,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__2_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 74, 111, 98, 65, 99, 116, 105, 111, 110, 46, 114, 101, 117, 115,
            101, 0,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__4_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 97, 107, 101, 46, 74, 111, 98, 65, 99, 116, 105, 111, 110, 46, 114, 101, 112, 108,
            97, 121, 0,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__6_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 97, 107, 101, 46, 74, 111, 98, 65, 99, 116, 105, 111, 110, 46, 117, 110, 112, 97,
            99, 107, 0,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__8_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 74, 111, 98, 65, 99, 116, 105, 111, 110, 46, 102, 101, 116, 99,
            104, 0,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__10_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 74, 111, 98, 65, 99, 116, 105, 111, 110, 46, 98, 117, 105, 108,
            100, 0,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprJobAction_repr___closed__11_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprJobAction_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprJobAction_repr___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprJobAction_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprJobAction_repr___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprJobAction_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprJobAction___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprJobAction_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprJobAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprJobAction: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprJobAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instOrdJobAction___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instOrdJobAction_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instOrdJobAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdJobAction___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instOrdJobAction: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdJobAction___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_JobAction_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_JobAction_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_JobAction_instMin___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JobAction_instMin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JobAction_instMin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_instMin___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_JobAction_instMin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_instMin___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_instMax___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JobAction_instMax___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JobAction_instMax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_instMax___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_JobAction_instMax: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_instMax___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [82, 97, 110, 0],
    };
static mut l_Lake_JobAction_verb___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__1_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [82, 117, 110, 110, 105, 110, 103, 0],
    };
static mut l_Lake_JobAction_verb___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [82, 101, 117, 115, 101, 100, 0],
    };
static mut l_Lake_JobAction_verb___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__3_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [82, 101, 117, 115, 105, 110, 103, 0],
    };
static mut l_Lake_JobAction_verb___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [82, 101, 112, 108, 97, 121, 101, 100, 0],
    };
static mut l_Lake_JobAction_verb___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__5_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [82, 101, 112, 108, 97, 121, 105, 110, 103, 0],
    };
static mut l_Lake_JobAction_verb___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__6_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [85, 110, 112, 97, 99, 107, 101, 100, 0],
    };
static mut l_Lake_JobAction_verb___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__7_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [85, 110, 112, 97, 99, 107, 105, 110, 103, 0],
    };
static mut l_Lake_JobAction_verb___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__8_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [70, 101, 116, 99, 104, 101, 100, 0],
    };
static mut l_Lake_JobAction_verb___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__9_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [70, 101, 116, 99, 104, 105, 110, 103, 0],
    };
static mut l_Lake_JobAction_verb___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__10_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [66, 117, 105, 108, 116, 0],
    };
static mut l_Lake_JobAction_verb___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_JobAction_verb___closed__11_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [66, 117, 105, 108, 100, 105, 110, 103, 0],
    };
static mut l_Lake_JobAction_verb___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JobAction_verb___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedJobState_default___closed__0_value: crate::leanh::LeanArrayObject<
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
static mut l_Lake_instInhabitedJobState_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedJobState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedJobState_default___closed__1_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [60, 110, 105, 108, 62, 0],
};
static mut l_Lake_instInhabitedJobState_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedJobState_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedJobState_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedJobState_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedJobState_default___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedJobState_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedJobState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedJobState: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedJob___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedJob___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedJob___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedJob___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedJob___closed__2_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lake_instInhabitedJob___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedJob___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedJob___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedJob___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Job_instPure___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Job_instPure___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Job_instPure___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_instPure___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Job_instPure: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_instPure___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_instFunctor___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Job_instFunctor___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Job_instFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_instFunctor___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Lake_Job_instFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Job_instFunctor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_instFunctor___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Job_instFunctor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Job_instFunctor: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_instFunctor___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0_value:
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
    m_fun: l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instCoeOutJobOpaqueJob___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Lake_Job_toOpaque as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_instCoeOutJobOpaqueJob___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instCoeOutJobOpaqueJob___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_JobAction_ctorIdx(mut v_x_920_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_920_ {
        0 => {
            let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_921_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_921_;
        }
        1 => {
            let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_922_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_922_;
        }
        2 => {
            let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_923_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_923_;
        }
        3 => {
            let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_924_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_924_;
        }
        4 => {
            let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_925_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_925_;
        }
        _ => {
            let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_926_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_926_;
        }
    }
}
pub unsafe fn l_Lake_JobAction_ctorIdx___boxed(
    mut v_x_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_928_: u8 = 0;
    let mut v_res_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_928_ = (crate::leanh::lean_unbox(v_x_927_) as u8);
    v_res_929_ = l_Lake_JobAction_ctorIdx(v_x_boxed_928_);
    return v_res_929_;
}
pub unsafe fn l_Lake_JobAction_toCtorIdx(mut v_x_930_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = l_Lake_JobAction_ctorIdx(v_x_930_);
    return v___x_931_;
}
pub unsafe fn l_Lake_JobAction_toCtorIdx___boxed(
    mut v_x_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_933_: u8 = 0;
    let mut v_res_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_933_ = (crate::leanh::lean_unbox(v_x_932_) as u8);
    v_res_934_ = l_Lake_JobAction_toCtorIdx(v_x_4__boxed_933_);
    return v_res_934_;
}
pub unsafe fn l_Lake_JobAction_ctorElim___redArg(
    mut v_k_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_935_);
    return v_k_935_;
}
pub unsafe fn l_Lake_JobAction_ctorElim___redArg___boxed(
    mut v_k_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_937_ = l_Lake_JobAction_ctorElim___redArg(v_k_936_);
    crate::leanh::lean_dec(v_k_936_);
    return v_res_937_;
}
pub unsafe fn l_Lake_JobAction_ctorElim(
    mut v_motive_938_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_939_: *mut crate::leanh::LeanObject,
    mut v_t_940_: u8,
    mut v_h_941_: *mut crate::leanh::LeanObject,
    mut v_k_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_942_);
    return v_k_942_;
}
pub unsafe fn l_Lake_JobAction_ctorElim___boxed(
    mut v_motive_943_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_944_: *mut crate::leanh::LeanObject,
    mut v_t_945_: *mut crate::leanh::LeanObject,
    mut v_h_946_: *mut crate::leanh::LeanObject,
    mut v_k_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_948_: u8 = 0;
    let mut v_res_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_948_ = (crate::leanh::lean_unbox(v_t_945_) as u8);
    v_res_949_ = l_Lake_JobAction_ctorElim(
        v_motive_943_,
        v_ctorIdx_944_,
        v_t_boxed_948_,
        v_h_946_,
        v_k_947_,
    );
    crate::leanh::lean_dec(v_k_947_);
    crate::leanh::lean_dec(v_ctorIdx_944_);
    return v_res_949_;
}
pub unsafe fn l_Lake_JobAction_unknown_elim___redArg(
    mut v_unknown_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unknown_950_);
    return v_unknown_950_;
}
pub unsafe fn l_Lake_JobAction_unknown_elim___redArg___boxed(
    mut v_unknown_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lake_JobAction_unknown_elim___redArg(v_unknown_951_);
    crate::leanh::lean_dec(v_unknown_951_);
    return v_res_952_;
}
pub unsafe fn l_Lake_JobAction_unknown_elim(
    mut v_motive_953_: *mut crate::leanh::LeanObject,
    mut v_t_954_: u8,
    mut v_h_955_: *mut crate::leanh::LeanObject,
    mut v_unknown_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unknown_956_);
    return v_unknown_956_;
}
pub unsafe fn l_Lake_JobAction_unknown_elim___boxed(
    mut v_motive_957_: *mut crate::leanh::LeanObject,
    mut v_t_958_: *mut crate::leanh::LeanObject,
    mut v_h_959_: *mut crate::leanh::LeanObject,
    mut v_unknown_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_961_: u8 = 0;
    let mut v_res_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_961_ = (crate::leanh::lean_unbox(v_t_958_) as u8);
    v_res_962_ =
        l_Lake_JobAction_unknown_elim(v_motive_957_, v_t_boxed_961_, v_h_959_, v_unknown_960_);
    crate::leanh::lean_dec(v_unknown_960_);
    return v_res_962_;
}
pub unsafe fn l_Lake_JobAction_reuse_elim___redArg(
    mut v_reuse_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reuse_963_);
    return v_reuse_963_;
}
pub unsafe fn l_Lake_JobAction_reuse_elim___redArg___boxed(
    mut v_reuse_964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_965_ = l_Lake_JobAction_reuse_elim___redArg(v_reuse_964_);
    crate::leanh::lean_dec(v_reuse_964_);
    return v_res_965_;
}
pub unsafe fn l_Lake_JobAction_reuse_elim(
    mut v_motive_966_: *mut crate::leanh::LeanObject,
    mut v_t_967_: u8,
    mut v_h_968_: *mut crate::leanh::LeanObject,
    mut v_reuse_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_reuse_969_);
    return v_reuse_969_;
}
pub unsafe fn l_Lake_JobAction_reuse_elim___boxed(
    mut v_motive_970_: *mut crate::leanh::LeanObject,
    mut v_t_971_: *mut crate::leanh::LeanObject,
    mut v_h_972_: *mut crate::leanh::LeanObject,
    mut v_reuse_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_974_: u8 = 0;
    let mut v_res_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_974_ = (crate::leanh::lean_unbox(v_t_971_) as u8);
    v_res_975_ = l_Lake_JobAction_reuse_elim(v_motive_970_, v_t_boxed_974_, v_h_972_, v_reuse_973_);
    crate::leanh::lean_dec(v_reuse_973_);
    return v_res_975_;
}
pub unsafe fn l_Lake_JobAction_replay_elim___redArg(
    mut v_replay_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_replay_976_);
    return v_replay_976_;
}
pub unsafe fn l_Lake_JobAction_replay_elim___redArg___boxed(
    mut v_replay_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Lake_JobAction_replay_elim___redArg(v_replay_977_);
    crate::leanh::lean_dec(v_replay_977_);
    return v_res_978_;
}
pub unsafe fn l_Lake_JobAction_replay_elim(
    mut v_motive_979_: *mut crate::leanh::LeanObject,
    mut v_t_980_: u8,
    mut v_h_981_: *mut crate::leanh::LeanObject,
    mut v_replay_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_replay_982_);
    return v_replay_982_;
}
pub unsafe fn l_Lake_JobAction_replay_elim___boxed(
    mut v_motive_983_: *mut crate::leanh::LeanObject,
    mut v_t_984_: *mut crate::leanh::LeanObject,
    mut v_h_985_: *mut crate::leanh::LeanObject,
    mut v_replay_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_987_: u8 = 0;
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_987_ = (crate::leanh::lean_unbox(v_t_984_) as u8);
    v_res_988_ =
        l_Lake_JobAction_replay_elim(v_motive_983_, v_t_boxed_987_, v_h_985_, v_replay_986_);
    crate::leanh::lean_dec(v_replay_986_);
    return v_res_988_;
}
pub unsafe fn l_Lake_JobAction_unpack_elim___redArg(
    mut v_unpack_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unpack_989_);
    return v_unpack_989_;
}
pub unsafe fn l_Lake_JobAction_unpack_elim___redArg___boxed(
    mut v_unpack_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lake_JobAction_unpack_elim___redArg(v_unpack_990_);
    crate::leanh::lean_dec(v_unpack_990_);
    return v_res_991_;
}
pub unsafe fn l_Lake_JobAction_unpack_elim(
    mut v_motive_992_: *mut crate::leanh::LeanObject,
    mut v_t_993_: u8,
    mut v_h_994_: *mut crate::leanh::LeanObject,
    mut v_unpack_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unpack_995_);
    return v_unpack_995_;
}
pub unsafe fn l_Lake_JobAction_unpack_elim___boxed(
    mut v_motive_996_: *mut crate::leanh::LeanObject,
    mut v_t_997_: *mut crate::leanh::LeanObject,
    mut v_h_998_: *mut crate::leanh::LeanObject,
    mut v_unpack_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1000_: u8 = 0;
    let mut v_res_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1000_ = (crate::leanh::lean_unbox(v_t_997_) as u8);
    v_res_1001_ =
        l_Lake_JobAction_unpack_elim(v_motive_996_, v_t_boxed_1000_, v_h_998_, v_unpack_999_);
    crate::leanh::lean_dec(v_unpack_999_);
    return v_res_1001_;
}
pub unsafe fn l_Lake_JobAction_fetch_elim___redArg(
    mut v_fetch_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_fetch_1002_);
    return v_fetch_1002_;
}
pub unsafe fn l_Lake_JobAction_fetch_elim___redArg___boxed(
    mut v_fetch_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1004_ = l_Lake_JobAction_fetch_elim___redArg(v_fetch_1003_);
    crate::leanh::lean_dec(v_fetch_1003_);
    return v_res_1004_;
}
pub unsafe fn l_Lake_JobAction_fetch_elim(
    mut v_motive_1005_: *mut crate::leanh::LeanObject,
    mut v_t_1006_: u8,
    mut v_h_1007_: *mut crate::leanh::LeanObject,
    mut v_fetch_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_fetch_1008_);
    return v_fetch_1008_;
}
pub unsafe fn l_Lake_JobAction_fetch_elim___boxed(
    mut v_motive_1009_: *mut crate::leanh::LeanObject,
    mut v_t_1010_: *mut crate::leanh::LeanObject,
    mut v_h_1011_: *mut crate::leanh::LeanObject,
    mut v_fetch_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1013_: u8 = 0;
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1013_ = (crate::leanh::lean_unbox(v_t_1010_) as u8);
    v_res_1014_ =
        l_Lake_JobAction_fetch_elim(v_motive_1009_, v_t_boxed_1013_, v_h_1011_, v_fetch_1012_);
    crate::leanh::lean_dec(v_fetch_1012_);
    return v_res_1014_;
}
pub unsafe fn l_Lake_JobAction_build_elim___redArg(
    mut v_build_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_build_1015_);
    return v_build_1015_;
}
pub unsafe fn l_Lake_JobAction_build_elim___redArg___boxed(
    mut v_build_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_Lake_JobAction_build_elim___redArg(v_build_1016_);
    crate::leanh::lean_dec(v_build_1016_);
    return v_res_1017_;
}
pub unsafe fn l_Lake_JobAction_build_elim(
    mut v_motive_1018_: *mut crate::leanh::LeanObject,
    mut v_t_1019_: u8,
    mut v_h_1020_: *mut crate::leanh::LeanObject,
    mut v_build_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_build_1021_);
    return v_build_1021_;
}
pub unsafe fn l_Lake_JobAction_build_elim___boxed(
    mut v_motive_1022_: *mut crate::leanh::LeanObject,
    mut v_t_1023_: *mut crate::leanh::LeanObject,
    mut v_h_1024_: *mut crate::leanh::LeanObject,
    mut v_build_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1026_: u8 = 0;
    let mut v_res_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1026_ = (crate::leanh::lean_unbox(v_t_1023_) as u8);
    v_res_1027_ =
        l_Lake_JobAction_build_elim(v_motive_1022_, v_t_boxed_1026_, v_h_1024_, v_build_1025_);
    crate::leanh::lean_dec(v_build_1025_);
    return v_res_1027_;
}
pub unsafe fn _init_l_Lake_instInhabitedJobAction_default() -> u8 {
    let mut v___x_1028_: u8 = 0;
    v___x_1028_ = 0;
    return v___x_1028_;
}
pub unsafe fn _init_l_Lake_instInhabitedJobAction() -> u8 {
    let mut v___x_1029_: u8 = 0;
    v___x_1029_ = 0;
    return v___x_1029_;
}
pub unsafe fn _init_l_Lake_instReprJobAction_repr___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1049_ = lean_nat_to_int(v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn _init_l_Lake_instReprJobAction_repr___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1051_ = lean_nat_to_int(v___x_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Lake_instReprJobAction_repr(
    mut v_x_1052_: u8,
    mut v_prec_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: u8 = 0;
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: u8 = 0;
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1052_ {
                0 => {
                    v___x_1096_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1097_ = lean_nat_dec_le(v___x_1096_, v_prec_1053_);
                    if v___x_1097_ == 0 {
                        v___x_1098_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__12_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__12,
                        );
                        v___y_1055_ = v___x_1098_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1099_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__13_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__13,
                        );
                        v___y_1055_ = v___x_1099_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1100_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1101_ = lean_nat_dec_le(v___x_1100_, v_prec_1053_);
                    if v___x_1101_ == 0 {
                        v___x_1102_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__12_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__12,
                        );
                        v___y_1062_ = v___x_1102_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1103_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__13_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__13,
                        );
                        v___y_1062_ = v___x_1103_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_1104_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1105_ = lean_nat_dec_le(v___x_1104_, v_prec_1053_);
                    if v___x_1105_ == 0 {
                        v___x_1106_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__12_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__12,
                        );
                        v___y_1069_ = v___x_1106_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1107_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__13_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__13,
                        );
                        v___y_1069_ = v___x_1107_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_1108_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1109_ = lean_nat_dec_le(v___x_1108_, v_prec_1053_);
                    if v___x_1109_ == 0 {
                        v___x_1110_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__12_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__12,
                        );
                        v___y_1076_ = v___x_1110_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1111_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__13_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__13,
                        );
                        v___y_1076_ = v___x_1111_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_1112_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1113_ = lean_nat_dec_le(v___x_1112_, v_prec_1053_);
                    if v___x_1113_ == 0 {
                        v___x_1114_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__12_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__12,
                        );
                        v___y_1083_ = v___x_1114_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1115_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__13_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__13,
                        );
                        v___y_1083_ = v___x_1115_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v___x_1116_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1117_ = lean_nat_dec_le(v___x_1116_, v_prec_1053_);
                    if v___x_1117_ == 0 {
                        v___x_1118_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__12),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__12_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__12,
                        );
                        v___y_1090_ = v___x_1118_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1119_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprJobAction_repr___closed__13),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprJobAction_repr___closed__13_once
                            ),
                            _init_l_Lake_instReprJobAction_repr___closed__13,
                        );
                        v___y_1090_ = v___x_1119_;
                        state = 6;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1056_ = l_Lake_instReprJobAction_repr___closed__1;
                crate::leanh::lean_inc(v___y_1055_);
                v___x_1057_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1057_, 0, v___y_1055_);
                crate::leanh::lean_ctor_set(v___x_1057_, 1, v___x_1056_);
                v___x_1058_ = 0;
                v___x_1059_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1059_, 0, v___x_1057_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1059_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1058_,
                );
                v___x_1060_ = l_Repr_addAppParen(v___x_1059_, v_prec_1053_);
                return v___x_1060_;
            }
            2 => {
                v___x_1063_ = l_Lake_instReprJobAction_repr___closed__3;
                crate::leanh::lean_inc(v___y_1062_);
                v___x_1064_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1064_, 0, v___y_1062_);
                crate::leanh::lean_ctor_set(v___x_1064_, 1, v___x_1063_);
                v___x_1065_ = 0;
                v___x_1066_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1064_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1066_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1065_,
                );
                v___x_1067_ = l_Repr_addAppParen(v___x_1066_, v_prec_1053_);
                return v___x_1067_;
            }
            3 => {
                v___x_1070_ = l_Lake_instReprJobAction_repr___closed__5;
                crate::leanh::lean_inc(v___y_1069_);
                v___x_1071_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1071_, 0, v___y_1069_);
                crate::leanh::lean_ctor_set(v___x_1071_, 1, v___x_1070_);
                v___x_1072_ = 0;
                v___x_1073_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1071_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1073_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1072_,
                );
                v___x_1074_ = l_Repr_addAppParen(v___x_1073_, v_prec_1053_);
                return v___x_1074_;
            }
            4 => {
                v___x_1077_ = l_Lake_instReprJobAction_repr___closed__7;
                crate::leanh::lean_inc(v___y_1076_);
                v___x_1078_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1078_, 0, v___y_1076_);
                crate::leanh::lean_ctor_set(v___x_1078_, 1, v___x_1077_);
                v___x_1079_ = 0;
                v___x_1080_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1078_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1080_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1079_,
                );
                v___x_1081_ = l_Repr_addAppParen(v___x_1080_, v_prec_1053_);
                return v___x_1081_;
            }
            5 => {
                v___x_1084_ = l_Lake_instReprJobAction_repr___closed__9;
                crate::leanh::lean_inc(v___y_1083_);
                v___x_1085_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1085_, 0, v___y_1083_);
                crate::leanh::lean_ctor_set(v___x_1085_, 1, v___x_1084_);
                v___x_1086_ = 0;
                v___x_1087_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1087_, 0, v___x_1085_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1087_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1086_,
                );
                v___x_1088_ = l_Repr_addAppParen(v___x_1087_, v_prec_1053_);
                return v___x_1088_;
            }
            6 => {
                v___x_1091_ = l_Lake_instReprJobAction_repr___closed__11;
                crate::leanh::lean_inc(v___y_1090_);
                v___x_1092_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1092_, 0, v___y_1090_);
                crate::leanh::lean_ctor_set(v___x_1092_, 1, v___x_1091_);
                v___x_1093_ = 0;
                v___x_1094_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1092_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1094_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1093_,
                );
                v___x_1095_ = l_Repr_addAppParen(v___x_1094_, v_prec_1053_);
                return v___x_1095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprJobAction_repr___boxed(
    mut v_x_1120_: *mut crate::leanh::LeanObject,
    mut v_prec_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_345__boxed_1122_: u8 = 0;
    let mut v_res_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_345__boxed_1122_ = (crate::leanh::lean_unbox(v_x_1120_) as u8);
    v_res_1123_ = l_Lake_instReprJobAction_repr(v_x_345__boxed_1122_, v_prec_1121_);
    crate::leanh::lean_dec(v_prec_1121_);
    return v_res_1123_;
}
pub unsafe fn l_Lake_JobAction_ofNat(mut v_n_1126_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: u8 = 0;
    v___x_1127_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1128_ = lean_nat_dec_le(v_n_1126_, v___x_1127_);
    if v___x_1128_ == 0 {
        let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1130_: u8 = 0;
        v___x_1129_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1130_ = lean_nat_dec_le(v_n_1126_, v___x_1129_);
        if v___x_1130_ == 0 {
            let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1132_: u8 = 0;
            v___x_1131_ = crate::leanh::lean_unsigned_to_nat(4);
            v___x_1132_ = lean_nat_dec_le(v_n_1126_, v___x_1131_);
            if v___x_1132_ == 0 {
                let mut v___x_1133_: u8 = 0;
                v___x_1133_ = 5;
                return v___x_1133_;
            } else {
                let mut v___x_1134_: u8 = 0;
                v___x_1134_ = 4;
                return v___x_1134_;
            }
        } else {
            let mut v___x_1135_: u8 = 0;
            v___x_1135_ = 3;
            return v___x_1135_;
        }
    } else {
        let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: u8 = 0;
        v___x_1136_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1137_ = lean_nat_dec_le(v_n_1126_, v___x_1136_);
        if v___x_1137_ == 0 {
            let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1139_: u8 = 0;
            v___x_1138_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1139_ = lean_nat_dec_le(v_n_1126_, v___x_1138_);
            if v___x_1139_ == 0 {
                let mut v___x_1140_: u8 = 0;
                v___x_1140_ = 2;
                return v___x_1140_;
            } else {
                let mut v___x_1141_: u8 = 0;
                v___x_1141_ = 1;
                return v___x_1141_;
            }
        } else {
            let mut v___x_1142_: u8 = 0;
            v___x_1142_ = 0;
            return v___x_1142_;
        }
    }
}
pub unsafe fn l_Lake_JobAction_ofNat___boxed(
    mut v_n_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1144_: u8 = 0;
    let mut v_r_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1144_ = l_Lake_JobAction_ofNat(v_n_1143_);
    crate::leanh::lean_dec(v_n_1143_);
    v_r_1145_ = crate::leanh::lean_box((v_res_1144_) as usize);
    return v_r_1145_;
}
pub unsafe fn l_Lake_instDecidableEqJobAction(mut v_x_1146_: u8, mut v_y_1147_: u8) -> u8 {
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    v___x_1148_ = l_Lake_JobAction_ctorIdx(v_x_1146_);
    v___x_1149_ = l_Lake_JobAction_ctorIdx(v_y_1147_);
    v___x_1150_ = lean_nat_dec_eq(v___x_1148_, v___x_1149_);
    crate::leanh::lean_dec(v___x_1149_);
    crate::leanh::lean_dec(v___x_1148_);
    return v___x_1150_;
}
pub unsafe fn l_Lake_instDecidableEqJobAction___boxed(
    mut v_x_1151_: *mut crate::leanh::LeanObject,
    mut v_y_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_1153_: u8 = 0;
    let mut v_y_14__boxed_1154_: u8 = 0;
    let mut v_res_1155_: u8 = 0;
    let mut v_r_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_1153_ = (crate::leanh::lean_unbox(v_x_1151_) as u8);
    v_y_14__boxed_1154_ = (crate::leanh::lean_unbox(v_y_1152_) as u8);
    v_res_1155_ = l_Lake_instDecidableEqJobAction(v_x_13__boxed_1153_, v_y_14__boxed_1154_);
    v_r_1156_ = crate::leanh::lean_box((v_res_1155_) as usize);
    return v_r_1156_;
}
pub unsafe fn l_Lake_instOrdJobAction_ord(mut v_x_1157_: u8, mut v_y_1158_: u8) -> u8 {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u8 = 0;
    v___x_1159_ = l_Lake_JobAction_ctorIdx(v_x_1157_);
    v___x_1160_ = l_Lake_JobAction_ctorIdx(v_y_1158_);
    v___x_1161_ = lean_nat_dec_lt(v___x_1159_, v___x_1160_);
    if v___x_1161_ == 0 {
        let mut v___x_1162_: u8 = 0;
        v___x_1162_ = lean_nat_dec_eq(v___x_1159_, v___x_1160_);
        crate::leanh::lean_dec(v___x_1160_);
        crate::leanh::lean_dec(v___x_1159_);
        if v___x_1162_ == 0 {
            let mut v___x_1163_: u8 = 0;
            v___x_1163_ = 2;
            return v___x_1163_;
        } else {
            let mut v___x_1164_: u8 = 0;
            v___x_1164_ = 1;
            return v___x_1164_;
        }
    } else {
        let mut v___x_1165_: u8 = 0;
        crate::leanh::lean_dec(v___x_1160_);
        crate::leanh::lean_dec(v___x_1159_);
        v___x_1165_ = 0;
        return v___x_1165_;
    }
}
pub unsafe fn l_Lake_instOrdJobAction_ord___boxed(
    mut v_x_1166_: *mut crate::leanh::LeanObject,
    mut v_y_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_1168_: u8 = 0;
    let mut v_y_31__boxed_1169_: u8 = 0;
    let mut v_res_1170_: u8 = 0;
    let mut v_r_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_1168_ = (crate::leanh::lean_unbox(v_x_1166_) as u8);
    v_y_31__boxed_1169_ = (crate::leanh::lean_unbox(v_y_1167_) as u8);
    v_res_1170_ = l_Lake_instOrdJobAction_ord(v_x_30__boxed_1168_, v_y_31__boxed_1169_);
    v_r_1171_ = crate::leanh::lean_box((v_res_1170_) as usize);
    return v_r_1171_;
}
pub unsafe fn _init_l_Lake_JobAction_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = crate::leanh::lean_box(0);
    return v___x_1174_;
}
pub unsafe fn _init_l_Lake_JobAction_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_box(0);
    return v___x_1175_;
}
pub unsafe fn l_Lake_JobAction_instMin___lam__0(mut v_x_1176_: u8, mut v_y_1177_: u8) -> u8 {
    let mut v___x_1178_: u8 = 0;
    v___x_1178_ = l_Lake_instOrdJobAction_ord(v_x_1176_, v_y_1177_);
    if v___x_1178_ == 2 {
        return v_y_1177_;
    } else {
        return v_x_1176_;
    }
}
pub unsafe fn l_Lake_JobAction_instMin___lam__0___boxed(
    mut v_x_1179_: *mut crate::leanh::LeanObject,
    mut v_y_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1181_: u8 = 0;
    let mut v_y_boxed_1182_: u8 = 0;
    let mut v_res_1183_: u8 = 0;
    let mut v_r_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1181_ = (crate::leanh::lean_unbox(v_x_1179_) as u8);
    v_y_boxed_1182_ = (crate::leanh::lean_unbox(v_y_1180_) as u8);
    v_res_1183_ = l_Lake_JobAction_instMin___lam__0(v_x_boxed_1181_, v_y_boxed_1182_);
    v_r_1184_ = crate::leanh::lean_box((v_res_1183_) as usize);
    return v_r_1184_;
}
pub unsafe fn l_Lake_JobAction_instMax___lam__0(mut v_x_1187_: u8, mut v_y_1188_: u8) -> u8 {
    let mut v___x_1189_: u8 = 0;
    v___x_1189_ = l_Lake_instOrdJobAction_ord(v_x_1187_, v_y_1188_);
    if v___x_1189_ == 2 {
        return v_x_1187_;
    } else {
        return v_y_1188_;
    }
}
pub unsafe fn l_Lake_JobAction_instMax___lam__0___boxed(
    mut v_x_1190_: *mut crate::leanh::LeanObject,
    mut v_y_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1192_: u8 = 0;
    let mut v_y_boxed_1193_: u8 = 0;
    let mut v_res_1194_: u8 = 0;
    let mut v_r_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1192_ = (crate::leanh::lean_unbox(v_x_1190_) as u8);
    v_y_boxed_1193_ = (crate::leanh::lean_unbox(v_y_1191_) as u8);
    v_res_1194_ = l_Lake_JobAction_instMax___lam__0(v_x_boxed_1192_, v_y_boxed_1193_);
    v_r_1195_ = crate::leanh::lean_box((v_res_1194_) as usize);
    return v_r_1195_;
}
pub unsafe fn l_Lake_JobAction_merge(mut v_a_1198_: u8, mut v_b_1199_: u8) -> u8 {
    let mut v___x_1200_: u8 = 0;
    v___x_1200_ = l_Lake_instOrdJobAction_ord(v_a_1198_, v_b_1199_);
    if v___x_1200_ == 2 {
        return v_a_1198_;
    } else {
        return v_b_1199_;
    }
}
pub unsafe fn l_Lake_JobAction_merge___boxed(
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_b_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1203_: u8 = 0;
    let mut v_b_boxed_1204_: u8 = 0;
    let mut v_res_1205_: u8 = 0;
    let mut v_r_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1203_ = (crate::leanh::lean_unbox(v_a_1201_) as u8);
    v_b_boxed_1204_ = (crate::leanh::lean_unbox(v_b_1202_) as u8);
    v_res_1205_ = l_Lake_JobAction_merge(v_a_boxed_1203_, v_b_boxed_1204_);
    v_r_1206_ = crate::leanh::lean_box((v_res_1205_) as usize);
    return v_r_1206_;
}
pub unsafe fn l_Lake_JobAction_verb(
    mut v_failed_1219_: u8,
    mut v_x_1220_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1220_ {
        0 => {
            if v_failed_1219_ == 0 {
                let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1221_ = l_Lake_JobAction_verb___closed__0;
                return v___x_1221_;
            } else {
                let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1222_ = l_Lake_JobAction_verb___closed__1;
                return v___x_1222_;
            }
        }
        1 => {
            if v_failed_1219_ == 0 {
                let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1223_ = l_Lake_JobAction_verb___closed__2;
                return v___x_1223_;
            } else {
                let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1224_ = l_Lake_JobAction_verb___closed__3;
                return v___x_1224_;
            }
        }
        2 => {
            if v_failed_1219_ == 0 {
                let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1225_ = l_Lake_JobAction_verb___closed__4;
                return v___x_1225_;
            } else {
                let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1226_ = l_Lake_JobAction_verb___closed__5;
                return v___x_1226_;
            }
        }
        3 => {
            if v_failed_1219_ == 0 {
                let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1227_ = l_Lake_JobAction_verb___closed__6;
                return v___x_1227_;
            } else {
                let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1228_ = l_Lake_JobAction_verb___closed__7;
                return v___x_1228_;
            }
        }
        4 => {
            if v_failed_1219_ == 0 {
                let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1229_ = l_Lake_JobAction_verb___closed__8;
                return v___x_1229_;
            } else {
                let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1230_ = l_Lake_JobAction_verb___closed__9;
                return v___x_1230_;
            }
        }
        _ => {
            if v_failed_1219_ == 0 {
                let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1231_ = l_Lake_JobAction_verb___closed__10;
                return v___x_1231_;
            } else {
                let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1232_ = l_Lake_JobAction_verb___closed__11;
                return v___x_1232_;
            }
        }
    }
}
pub unsafe fn l_Lake_JobAction_verb___boxed(
    mut v_failed_1233_: *mut crate::leanh::LeanObject,
    mut v_x_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failed_boxed_1235_: u8 = 0;
    let mut v_x_256__boxed_1236_: u8 = 0;
    let mut v_res_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failed_boxed_1235_ = (crate::leanh::lean_unbox(v_failed_1233_) as u8);
    v_x_256__boxed_1236_ = (crate::leanh::lean_unbox(v_x_1234_) as u8);
    v_res_1237_ = l_Lake_JobAction_verb(v_failed_boxed_1235_, v_x_256__boxed_1236_);
    return v_res_1237_;
}
pub unsafe fn _init_l_Lake_instInhabitedJobState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1241_ = l_Lake_instInhabitedJobState_default___closed__1;
    v___x_1242_ = l_Lake_BuildTrace_nil(v___x_1241_);
    return v___x_1242_;
}
pub unsafe fn _init_l_Lake_instInhabitedJobState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2_once),
        _init_l_Lake_instInhabitedJobState_default___closed__2,
    );
    v___x_1245_ = 0;
    v___x_1246_ = 0;
    v___x_1247_ = l_Lake_instInhabitedJobState_default___closed__0;
    v___x_1248_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    crate::leanh::lean_ctor_set(v___x_1248_, 1, v___x_1244_);
    crate::leanh::lean_ctor_set(v___x_1248_, 2, v___x_1243_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1248_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1246_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1248_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1245_,
    );
    return v___x_1248_;
}
pub unsafe fn _init_l_Lake_instInhabitedJobState_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__3_once),
        _init_l_Lake_instInhabitedJobState_default___closed__3,
    );
    return v___x_1249_;
}
pub unsafe fn _init_l_Lake_instInhabitedJobState() -> *mut crate::leanh::LeanObject {
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Lake_instInhabitedJobState_default;
    return v___x_1250_;
}
pub unsafe fn l_Lake_JobState_merge(
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_b_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1254_: u8 = 0;
    let mut v_wantsRebuild_1255_: u8 = 0;
    let mut v_trace_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1259_: u8 = 0;
    let mut v_wantsRebuild_1260_: u8 = 0;
    let mut v_trace_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    let mut v___y_1269_: u8 = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_1253_ = crate::leanh::lean_ctor_get(v_a_1251_, 0);
                crate::leanh::lean_inc_ref(v_log_1253_);
                v_action_1254_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1255_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1256_ = crate::leanh::lean_ctor_get(v_a_1251_, 1);
                crate::leanh::lean_inc_ref(v_trace_1256_);
                v_buildTime_1257_ = crate::leanh::lean_ctor_get(v_a_1251_, 2);
                crate::leanh::lean_inc(v_buildTime_1257_);
                crate::leanh::lean_dec_ref(v_a_1251_);
                v_log_1258_ = crate::leanh::lean_ctor_get(v_b_1252_, 0);
                v_action_1259_ = crate::leanh::lean_ctor_get_uint8(
                    v_b_1252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1260_ = crate::leanh::lean_ctor_get_uint8(
                    v_b_1252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1261_ = crate::leanh::lean_ctor_get(v_b_1252_, 1);
                v_buildTime_1262_ = crate::leanh::lean_ctor_get(v_b_1252_, 2);
                v_isSharedCheck_1275_ = (!crate::leanh::lean_is_exclusive(v_b_1252_)) as u8;
                if v_isSharedCheck_1275_ == 0 {
                    v___x_1264_ = v_b_1252_;
                    v_isShared_1265_ = v_isSharedCheck_1275_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1262_);
                    crate::leanh::lean_inc(v_trace_1261_);
                    crate::leanh::lean_inc(v_log_1258_);
                    crate::leanh::lean_dec(v_b_1252_);
                    v___x_1264_ = crate::leanh::lean_box(0);
                    v_isShared_1265_ = v_isSharedCheck_1275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1266_ = l_Array_append___redArg(v_log_1253_, v_log_1258_);
                crate::leanh::lean_dec_ref(v_log_1258_);
                v___x_1267_ = l_Lake_JobAction_merge(v_action_1254_, v_action_1259_);
                if v_wantsRebuild_1255_ == 0 {
                    v___y_1269_ = v_wantsRebuild_1260_;
                    state = 2;
                    continue;
                } else {
                    v___y_1269_ = v_wantsRebuild_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = l_Lake_BuildTrace_mix(v_trace_1256_, v_trace_1261_);
                v___x_1271_ = lean_nat_add(v_buildTime_1257_, v_buildTime_1262_);
                crate::leanh::lean_dec(v_buildTime_1262_);
                crate::leanh::lean_dec(v_buildTime_1257_);
                if v_isShared_1265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1264_, 2, v___x_1271_);
                    crate::leanh::lean_ctor_set(v___x_1264_, 1, v___x_1270_);
                    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1266_);
                    v___x_1273_ = v___x_1264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1267_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_1269_,
                );
                return v___x_1273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JobState_modifyLog(
    mut v_f_1276_: *mut crate::leanh::LeanObject,
    mut v_s_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1279_: u8 = 0;
    let mut v_wantsRebuild_1280_: u8 = 0;
    let mut v_trace_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_1278_ = crate::leanh::lean_ctor_get(v_s_1277_, 0);
                v_action_1279_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1280_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1281_ = crate::leanh::lean_ctor_get(v_s_1277_, 1);
                v_buildTime_1282_ = crate::leanh::lean_ctor_get(v_s_1277_, 2);
                v_isSharedCheck_1290_ = (!crate::leanh::lean_is_exclusive(v_s_1277_)) as u8;
                if v_isSharedCheck_1290_ == 0 {
                    v___x_1284_ = v_s_1277_;
                    v_isShared_1285_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1282_);
                    crate::leanh::lean_inc(v_trace_1281_);
                    crate::leanh::lean_inc(v_log_1278_);
                    crate::leanh::lean_dec(v_s_1277_);
                    v___x_1284_ = crate::leanh::lean_box(0);
                    v_isShared_1285_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1286_ = crate::leanh::lean_apply_1(v_f_1276_, v_log_1278_);
                if v_isShared_1285_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1286_);
                    v___x_1288_ = v___x_1284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1289_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_trace_1281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_buildTime_1282_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1289_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1279_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1289_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1280_,
                    );
                    v___x_1288_ = v_reuseFailAlloc_1289_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JobState_logEntry(
    mut v_e_1291_: *mut crate::leanh::LeanObject,
    mut v_s_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1294_: u8 = 0;
    let mut v_wantsRebuild_1295_: u8 = 0;
    let mut v_trace_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_1293_ = crate::leanh::lean_ctor_get(v_s_1292_, 0);
                v_action_1294_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1292_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1295_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1292_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1296_ = crate::leanh::lean_ctor_get(v_s_1292_, 1);
                v_buildTime_1297_ = crate::leanh::lean_ctor_get(v_s_1292_, 2);
                v_isSharedCheck_1305_ = (!crate::leanh::lean_is_exclusive(v_s_1292_)) as u8;
                if v_isSharedCheck_1305_ == 0 {
                    v___x_1299_ = v_s_1292_;
                    v_isShared_1300_ = v_isSharedCheck_1305_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1297_);
                    crate::leanh::lean_inc(v_trace_1296_);
                    crate::leanh::lean_inc(v_log_1293_);
                    crate::leanh::lean_dec(v_s_1292_);
                    v___x_1299_ = crate::leanh::lean_box(0);
                    v_isShared_1300_ = v_isSharedCheck_1305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1301_ = lean_array_push(v_log_1293_, v_e_1291_);
                if v_isShared_1300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1299_, 0, v___x_1301_);
                    v___x_1303_ = v___x_1299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1304_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_trace_1296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_buildTime_1297_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1304_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1294_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1304_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1295_,
                    );
                    v___x_1303_ = v_reuseFailAlloc_1304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JobResult_prependLog___redArg(
    mut v_log_1306_: *mut crate::leanh::LeanObject,
    mut v_self_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v_log_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1314_: u8 = 0;
    let mut v_wantsRebuild_1315_: u8 = 0;
    let mut v_trace_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v_log_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1336_: u8 = 0;
    let mut v_wantsRebuild_1337_: u8 = 0;
    let mut v_trace_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1342_: u8 = 0;
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_self_1307_) == 0 {
                    v_a_1308_ = crate::leanh::lean_ctor_get(v_self_1307_, 1);
                    v_a_1309_ = crate::leanh::lean_ctor_get(v_self_1307_, 0);
                    v_isSharedCheck_1329_ = (!crate::leanh::lean_is_exclusive(v_self_1307_)) as u8;
                    if v_isSharedCheck_1329_ == 0 {
                        v___x_1311_ = v_self_1307_;
                        v_isShared_1312_ = v_isSharedCheck_1329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1308_);
                        crate::leanh::lean_inc(v_a_1309_);
                        crate::leanh::lean_dec(v_self_1307_);
                        v___x_1311_ = crate::leanh::lean_box(0);
                        v_isShared_1312_ = v_isSharedCheck_1329_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1330_ = crate::leanh::lean_ctor_get(v_self_1307_, 1);
                    v_a_1331_ = crate::leanh::lean_ctor_get(v_self_1307_, 0);
                    v_isSharedCheck_1353_ = (!crate::leanh::lean_is_exclusive(v_self_1307_)) as u8;
                    if v_isSharedCheck_1353_ == 0 {
                        v___x_1333_ = v_self_1307_;
                        v_isShared_1334_ = v_isSharedCheck_1353_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1330_);
                        crate::leanh::lean_inc(v_a_1331_);
                        crate::leanh::lean_dec(v_self_1307_);
                        v___x_1333_ = crate::leanh::lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1353_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_log_1313_ = crate::leanh::lean_ctor_get(v_a_1308_, 0);
                v_action_1314_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1315_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1308_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1316_ = crate::leanh::lean_ctor_get(v_a_1308_, 1);
                v_buildTime_1317_ = crate::leanh::lean_ctor_get(v_a_1308_, 2);
                v_isSharedCheck_1328_ = (!crate::leanh::lean_is_exclusive(v_a_1308_)) as u8;
                if v_isSharedCheck_1328_ == 0 {
                    v___x_1319_ = v_a_1308_;
                    v_isShared_1320_ = v_isSharedCheck_1328_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1317_);
                    crate::leanh::lean_inc(v_trace_1316_);
                    crate::leanh::lean_inc(v_log_1313_);
                    crate::leanh::lean_dec(v_a_1308_);
                    v___x_1319_ = crate::leanh::lean_box(0);
                    v_isShared_1320_ = v_isSharedCheck_1328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1321_ = l_Array_append___redArg(v_log_1306_, v_log_1313_);
                crate::leanh::lean_dec_ref(v_log_1313_);
                if v_isShared_1320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1321_);
                    v___x_1323_ = v___x_1319_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_trace_1316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_buildTime_1317_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1327_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1314_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1327_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1315_,
                    );
                    v___x_1323_ = v_reuseFailAlloc_1327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1312_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1311_, 1, v___x_1323_);
                    v___x_1325_ = v___x_1311_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
                    v___x_1325_ = v_reuseFailAlloc_1326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1325_;
            }
            5 => {
                v_log_1335_ = crate::leanh::lean_ctor_get(v_a_1330_, 0);
                v_action_1336_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1330_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1337_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1330_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1338_ = crate::leanh::lean_ctor_get(v_a_1330_, 1);
                v_buildTime_1339_ = crate::leanh::lean_ctor_get(v_a_1330_, 2);
                v_isSharedCheck_1352_ = (!crate::leanh::lean_is_exclusive(v_a_1330_)) as u8;
                if v_isSharedCheck_1352_ == 0 {
                    v___x_1341_ = v_a_1330_;
                    v_isShared_1342_ = v_isSharedCheck_1352_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1339_);
                    crate::leanh::lean_inc(v_trace_1338_);
                    crate::leanh::lean_inc(v_log_1335_);
                    crate::leanh::lean_dec(v_a_1330_);
                    v___x_1341_ = crate::leanh::lean_box(0);
                    v_isShared_1342_ = v_isSharedCheck_1352_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1343_ = lean_array_get_size(v_log_1306_);
                v___x_1344_ = lean_nat_add(v___x_1343_, v_a_1331_);
                crate::leanh::lean_dec(v_a_1331_);
                v___x_1345_ = l_Array_append___redArg(v_log_1306_, v_log_1335_);
                crate::leanh::lean_dec_ref(v_log_1335_);
                if v_isShared_1342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1341_, 0, v___x_1345_);
                    v___x_1347_ = v___x_1341_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_trace_1338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_buildTime_1339_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1351_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1336_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1351_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1337_,
                    );
                    v___x_1347_ = v_reuseFailAlloc_1351_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1333_, 1, v___x_1347_);
                    crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1344_);
                    v___x_1349_ = v___x_1333_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1347_);
                    v___x_1349_ = v_reuseFailAlloc_1350_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JobResult_prependLog(
    mut v_00_u03b1_1354_: *mut crate::leanh::LeanObject,
    mut v_log_1355_: *mut crate::leanh::LeanObject,
    mut v_self_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Lake_JobResult_prependLog___redArg(v_log_1355_, v_self_1356_);
    return v___x_1357_;
}
pub unsafe fn _init_l_Lake_instInhabitedJob___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lake_instInhabitedJobState_default;
    v___x_1359_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1360_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    crate::leanh::lean_ctor_set(v___x_1360_, 1, v___x_1358_);
    return v___x_1360_;
}
pub unsafe fn _init_l_Lake_instInhabitedJob___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJob___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJob___closed__0_once),
        _init_l_Lake_instInhabitedJob___closed__0,
    );
    v___x_1362_ = lean_task_pure(v___x_1361_);
    return v___x_1362_;
}
pub unsafe fn _init_l_Lake_instInhabitedJob___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1364_ = 0;
    v___x_1365_ = l_Lake_instInhabitedJob___closed__2;
    v___x_1366_ = crate::leanh::lean_box(0);
    v___x_1367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJob___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJob___closed__1_once),
        _init_l_Lake_instInhabitedJob___closed__1,
    );
    v___x_1368_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1367_);
    crate::leanh::lean_ctor_set(v___x_1368_, 1, v___x_1366_);
    crate::leanh::lean_ctor_set(v___x_1368_, 2, v___x_1365_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1368_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1364_,
    );
    return v___x_1368_;
}
pub unsafe fn l_Lake_instInhabitedJob(
    mut v_00_u03b1_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJob___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJob___closed__3_once),
        _init_l_Lake_instInhabitedJob___closed__3,
    );
    return v___x_1370_;
}
pub unsafe fn l_Lake_Job_cast___redArg(
    mut v_self_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1371_);
    return v_self_1371_;
}
pub unsafe fn l_Lake_Job_cast___redArg___boxed(
    mut v_self_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Lake_Job_cast___redArg(v_self_1372_);
    crate::leanh::lean_dec_ref(v_self_1372_);
    return v_res_1373_;
}
pub unsafe fn l_Lake_Job_cast(
    mut v_00_u03b1_1374_: *mut crate::leanh::LeanObject,
    mut v_self_1375_: *mut crate::leanh::LeanObject,
    mut v_h_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1375_);
    return v_self_1375_;
}
pub unsafe fn l_Lake_Job_cast___boxed(
    mut v_00_u03b1_1377_: *mut crate::leanh::LeanObject,
    mut v_self_1378_: *mut crate::leanh::LeanObject,
    mut v_h_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1380_ = l_Lake_Job_cast(v_00_u03b1_1377_, v_self_1378_, v_h_1379_);
    crate::leanh::lean_dec_ref(v_self_1378_);
    return v_res_1380_;
}
pub unsafe fn l_Lake_Job_ofTask___redArg(
    mut v_inst_1381_: *mut crate::leanh::LeanObject,
    mut v_task_1382_: *mut crate::leanh::LeanObject,
    mut v_caption_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = 0;
    v___x_1385_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1385_, 0, v_task_1382_);
    crate::leanh::lean_ctor_set(v___x_1385_, 1, v_inst_1381_);
    crate::leanh::lean_ctor_set(v___x_1385_, 2, v_caption_1383_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1385_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1384_,
    );
    return v___x_1385_;
}
pub unsafe fn l_Lake_Job_ofTask(
    mut v_00_u03b1_1386_: *mut crate::leanh::LeanObject,
    mut v_inst_1387_: *mut crate::leanh::LeanObject,
    mut v_task_1388_: *mut crate::leanh::LeanObject,
    mut v_caption_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = 0;
    v___x_1391_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1391_, 0, v_task_1388_);
    crate::leanh::lean_ctor_set(v___x_1391_, 1, v_inst_1387_);
    crate::leanh::lean_ctor_set(v___x_1391_, 2, v_caption_1389_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1391_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1390_,
    );
    return v___x_1391_;
}
pub unsafe fn l_Lake_Job_error___redArg(
    mut v_inst_1392_: *mut crate::leanh::LeanObject,
    mut v_log_1393_: *mut crate::leanh::LeanObject,
    mut v_caption_1394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1396_ = 0;
    v___x_1397_ = 0;
    v___x_1398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2_once),
        _init_l_Lake_instInhabitedJobState_default___closed__2,
    );
    v___x_1399_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1399_, 0, v_log_1393_);
    crate::leanh::lean_ctor_set(v___x_1399_, 1, v___x_1398_);
    crate::leanh::lean_ctor_set(v___x_1399_, 2, v___x_1395_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1399_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1396_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1399_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1397_,
    );
    v___x_1400_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1395_);
    crate::leanh::lean_ctor_set(v___x_1400_, 1, v___x_1399_);
    v___x_1401_ = lean_task_pure(v___x_1400_);
    v___x_1402_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1402_, 0, v___x_1401_);
    crate::leanh::lean_ctor_set(v___x_1402_, 1, v_inst_1392_);
    crate::leanh::lean_ctor_set(v___x_1402_, 2, v_caption_1394_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1402_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1397_,
    );
    return v___x_1402_;
}
pub unsafe fn l_Lake_Job_error(
    mut v_00_u03b1_1403_: *mut crate::leanh::LeanObject,
    mut v_inst_1404_: *mut crate::leanh::LeanObject,
    mut v_log_1405_: *mut crate::leanh::LeanObject,
    mut v_caption_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1408_ = 0;
    v___x_1409_ = 0;
    v___x_1410_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2_once),
        _init_l_Lake_instInhabitedJobState_default___closed__2,
    );
    v___x_1411_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1411_, 0, v_log_1405_);
    crate::leanh::lean_ctor_set(v___x_1411_, 1, v___x_1410_);
    crate::leanh::lean_ctor_set(v___x_1411_, 2, v___x_1407_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1411_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1408_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1411_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1409_,
    );
    v___x_1412_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1412_, 0, v___x_1407_);
    crate::leanh::lean_ctor_set(v___x_1412_, 1, v___x_1411_);
    v___x_1413_ = lean_task_pure(v___x_1412_);
    v___x_1414_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1414_, 0, v___x_1413_);
    crate::leanh::lean_ctor_set(v___x_1414_, 1, v_inst_1404_);
    crate::leanh::lean_ctor_set(v___x_1414_, 2, v_caption_1406_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1414_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1409_,
    );
    return v___x_1414_;
}
pub unsafe fn l_Lake_Job_pure___redArg(
    mut v_kind_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
    mut v_log_1417_: *mut crate::leanh::LeanObject,
    mut v_caption_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = 0;
    v___x_1420_ = 0;
    v___x_1421_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2_once),
        _init_l_Lake_instInhabitedJobState_default___closed__2,
    );
    v___x_1422_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1423_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1423_, 0, v_log_1417_);
    crate::leanh::lean_ctor_set(v___x_1423_, 1, v___x_1421_);
    crate::leanh::lean_ctor_set(v___x_1423_, 2, v___x_1422_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1423_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1419_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1423_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1420_,
    );
    v___x_1424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1424_, 0, v_a_1416_);
    crate::leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
    v___x_1425_ = lean_task_pure(v___x_1424_);
    v___x_1426_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1425_);
    crate::leanh::lean_ctor_set(v___x_1426_, 1, v_kind_1415_);
    crate::leanh::lean_ctor_set(v___x_1426_, 2, v_caption_1418_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1426_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1420_,
    );
    return v___x_1426_;
}
pub unsafe fn l_Lake_Job_pure(
    mut v_00_u03b1_1427_: *mut crate::leanh::LeanObject,
    mut v_kind_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_log_1430_: *mut crate::leanh::LeanObject,
    mut v_caption_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = 0;
    v___x_1433_ = 0;
    v___x_1434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2_once),
        _init_l_Lake_instInhabitedJobState_default___closed__2,
    );
    v___x_1435_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1436_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1436_, 0, v_log_1430_);
    crate::leanh::lean_ctor_set(v___x_1436_, 1, v___x_1434_);
    crate::leanh::lean_ctor_set(v___x_1436_, 2, v___x_1435_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1436_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1432_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1436_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1433_,
    );
    v___x_1437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1437_, 0, v_a_1429_);
    crate::leanh::lean_ctor_set(v___x_1437_, 1, v___x_1436_);
    v___x_1438_ = lean_task_pure(v___x_1437_);
    v___x_1439_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 1, v_kind_1428_);
    crate::leanh::lean_ctor_set(v___x_1439_, 2, v_caption_1431_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1439_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1433_,
    );
    return v___x_1439_;
}
pub unsafe fn l_Lake_Job_instPure___lam__0(
    mut v_00_u03b1_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = crate::leanh::lean_box(0);
    v___x_1443_ = l_Lake_instInhabitedJob___closed__2;
    v___x_1444_ = 0;
    v___x_1445_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__3_once),
        _init_l_Lake_instInhabitedJobState_default___closed__3,
    );
    v___x_1446_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1446_, 0, v_a_1441_);
    crate::leanh::lean_ctor_set(v___x_1446_, 1, v___x_1445_);
    v___x_1447_ = lean_task_pure(v___x_1446_);
    v___x_1448_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1447_);
    crate::leanh::lean_ctor_set(v___x_1448_, 1, v___x_1442_);
    crate::leanh::lean_ctor_set(v___x_1448_, 2, v___x_1443_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1448_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1444_,
    );
    return v___x_1448_;
}
pub unsafe fn l_Lake_Job_traceRoot___redArg(
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_caption_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = crate::leanh::lean_box(0);
    v___x_1454_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1455_ = l_Lake_instInhabitedJobState_default___closed__0;
    v___x_1456_ = 0;
    v___x_1457_ = 0;
    v___x_1458_ = l_Lake_BuildTrace_nil(v_caption_1452_);
    v___x_1459_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1459_, 0, v___x_1455_);
    crate::leanh::lean_ctor_set(v___x_1459_, 1, v___x_1458_);
    crate::leanh::lean_ctor_set(v___x_1459_, 2, v___x_1454_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1459_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1456_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1459_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1457_,
    );
    v___x_1460_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1460_, 0, v_a_1451_);
    crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1459_);
    v___x_1461_ = lean_task_pure(v___x_1460_);
    v___x_1462_ = l_Lake_instInhabitedJob___closed__2;
    v___x_1463_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1463_, 0, v___x_1461_);
    crate::leanh::lean_ctor_set(v___x_1463_, 1, v___x_1453_);
    crate::leanh::lean_ctor_set(v___x_1463_, 2, v___x_1462_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1463_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1457_,
    );
    return v___x_1463_;
}
pub unsafe fn l_Lake_Job_traceRoot(
    mut v_00_u03b1_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
    mut v_caption_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = crate::leanh::lean_box(0);
    v___x_1468_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1469_ = l_Lake_instInhabitedJobState_default___closed__0;
    v___x_1470_ = 0;
    v___x_1471_ = 0;
    v___x_1472_ = l_Lake_BuildTrace_nil(v_caption_1466_);
    v___x_1473_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1473_, 0, v___x_1469_);
    crate::leanh::lean_ctor_set(v___x_1473_, 1, v___x_1472_);
    crate::leanh::lean_ctor_set(v___x_1473_, 2, v___x_1468_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1473_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1470_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1473_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1471_,
    );
    v___x_1474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1474_, 0, v_a_1465_);
    crate::leanh::lean_ctor_set(v___x_1474_, 1, v___x_1473_);
    v___x_1475_ = lean_task_pure(v___x_1474_);
    v___x_1476_ = l_Lake_instInhabitedJob___closed__2;
    v___x_1477_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1475_);
    crate::leanh::lean_ctor_set(v___x_1477_, 1, v___x_1467_);
    crate::leanh::lean_ctor_set(v___x_1477_, 2, v___x_1476_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1477_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1471_,
    );
    return v___x_1477_;
}
pub unsafe fn l_Lake_Job_nop(
    mut v_log_1478_: *mut crate::leanh::LeanObject,
    mut v_caption_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lake_instDataKindUnit;
    v___x_1481_ = crate::leanh::lean_box(0);
    v___x_1482_ = 0;
    v___x_1483_ = 0;
    v___x_1484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedJobState_default___closed__2_once),
        _init_l_Lake_instInhabitedJobState_default___closed__2,
    );
    v___x_1485_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1486_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1486_, 0, v_log_1478_);
    crate::leanh::lean_ctor_set(v___x_1486_, 1, v___x_1484_);
    crate::leanh::lean_ctor_set(v___x_1486_, 2, v___x_1485_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1486_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1482_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1486_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1483_,
    );
    v___x_1487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1481_);
    crate::leanh::lean_ctor_set(v___x_1487_, 1, v___x_1486_);
    v___x_1488_ = lean_task_pure(v___x_1487_);
    v___x_1489_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1489_, 0, v___x_1488_);
    crate::leanh::lean_ctor_set(v___x_1489_, 1, v___x_1480_);
    crate::leanh::lean_ctor_set(v___x_1489_, 2, v_caption_1479_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1489_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1483_,
    );
    return v___x_1489_;
}
pub unsafe fn l_Lake_Job_nil(
    mut v_traceCaption_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = crate::leanh::lean_box(0);
    v___x_1492_ = crate::leanh::lean_box(0);
    v___x_1493_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1494_ = l_Lake_instInhabitedJobState_default___closed__0;
    v___x_1495_ = 0;
    v___x_1496_ = 0;
    v___x_1497_ = l_Lake_BuildTrace_nil(v_traceCaption_1490_);
    v___x_1498_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1498_, 0, v___x_1494_);
    crate::leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    crate::leanh::lean_ctor_set(v___x_1498_, 2, v___x_1493_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1498_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1495_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1498_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1496_,
    );
    v___x_1499_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1499_, 0, v___x_1491_);
    crate::leanh::lean_ctor_set(v___x_1499_, 1, v___x_1498_);
    v___x_1500_ = lean_task_pure(v___x_1499_);
    v___x_1501_ = l_Lake_instInhabitedJob___closed__2;
    v___x_1502_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1502_, 0, v___x_1500_);
    crate::leanh::lean_ctor_set(v___x_1502_, 1, v___x_1492_);
    crate::leanh::lean_ctor_set(v___x_1502_, 2, v___x_1501_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1502_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1496_,
    );
    return v___x_1502_;
}
pub unsafe fn l_Lake_Job_getTrace___redArg(
    mut v_job_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_1504_ = crate::leanh::lean_ctor_get(v_job_1503_, 0);
    crate::leanh::lean_inc_ref(v_task_1504_);
    crate::leanh::lean_dec_ref(v_job_1503_);
    v___x_1505_ = lean_task_get_own(v_task_1504_);
    v_a_1506_ = crate::leanh::lean_ctor_get(v___x_1505_, 1);
    crate::leanh::lean_inc(v_a_1506_);
    crate::leanh::lean_dec(v___x_1505_);
    v_trace_1507_ = crate::leanh::lean_ctor_get(v_a_1506_, 1);
    crate::leanh::lean_inc_ref(v_trace_1507_);
    crate::leanh::lean_dec(v_a_1506_);
    return v_trace_1507_;
}
pub unsafe fn l_Lake_Job_getTrace(
    mut v_00_u03b1_1508_: *mut crate::leanh::LeanObject,
    mut v_job_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_1510_ = crate::leanh::lean_ctor_get(v_job_1509_, 0);
    crate::leanh::lean_inc_ref(v_task_1510_);
    crate::leanh::lean_dec_ref(v_job_1509_);
    v___x_1511_ = lean_task_get_own(v_task_1510_);
    v_a_1512_ = crate::leanh::lean_ctor_get(v___x_1511_, 1);
    crate::leanh::lean_inc(v_a_1512_);
    crate::leanh::lean_dec(v___x_1511_);
    v_trace_1513_ = crate::leanh::lean_ctor_get(v_a_1512_, 1);
    crate::leanh::lean_inc_ref(v_trace_1513_);
    crate::leanh::lean_dec(v_a_1512_);
    return v_trace_1513_;
}
pub unsafe fn l_Lake_Job_setCaption___redArg(
    mut v_caption_1514_: *mut crate::leanh::LeanObject,
    mut v_job_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1518_: u8 = 0;
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1521_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v_unused_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1516_ = crate::leanh::lean_ctor_get(v_job_1515_, 0);
                v_kind_1517_ = crate::leanh::lean_ctor_get(v_job_1515_, 1);
                v_optional_1518_ = crate::leanh::lean_ctor_get_uint8(
                    v_job_1515_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1525_ = (!crate::leanh::lean_is_exclusive(v_job_1515_)) as u8;
                if v_isSharedCheck_1525_ == 0 {
                    v_unused_1526_ = crate::leanh::lean_ctor_get(v_job_1515_, 2);
                    crate::leanh::lean_dec(v_unused_1526_);
                    v___x_1520_ = v_job_1515_;
                    v_isShared_1521_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_1517_);
                    crate::leanh::lean_inc(v_task_1516_);
                    crate::leanh::lean_dec(v_job_1515_);
                    v___x_1520_ = crate::leanh::lean_box(0);
                    v_isShared_1521_ = v_isSharedCheck_1525_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1520_, 2, v_caption_1514_);
                    v___x_1523_ = v___x_1520_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_task_1516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_kind_1517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_caption_1514_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1524_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1518_,
                    );
                    v___x_1523_ = v_reuseFailAlloc_1524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_setCaption(
    mut v_00_u03b1_1527_: *mut crate::leanh::LeanObject,
    mut v_caption_1528_: *mut crate::leanh::LeanObject,
    mut v_job_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1532_: u8 = 0;
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut v_unused_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1530_ = crate::leanh::lean_ctor_get(v_job_1529_, 0);
                v_kind_1531_ = crate::leanh::lean_ctor_get(v_job_1529_, 1);
                v_optional_1532_ = crate::leanh::lean_ctor_get_uint8(
                    v_job_1529_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1539_ = (!crate::leanh::lean_is_exclusive(v_job_1529_)) as u8;
                if v_isSharedCheck_1539_ == 0 {
                    v_unused_1540_ = crate::leanh::lean_ctor_get(v_job_1529_, 2);
                    crate::leanh::lean_dec(v_unused_1540_);
                    v___x_1534_ = v_job_1529_;
                    v_isShared_1535_ = v_isSharedCheck_1539_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_1531_);
                    crate::leanh::lean_inc(v_task_1530_);
                    crate::leanh::lean_dec(v_job_1529_);
                    v___x_1534_ = crate::leanh::lean_box(0);
                    v_isShared_1535_ = v_isSharedCheck_1539_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1534_, 2, v_caption_1528_);
                    v___x_1537_ = v___x_1534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_task_1530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_kind_1531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_caption_1528_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1538_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1532_,
                    );
                    v___x_1537_ = v_reuseFailAlloc_1538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_setCaption_x3f___redArg(
    mut v_caption_1541_: *mut crate::leanh::LeanObject,
    mut v_job_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1546_: u8 = 0;
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut v_unused_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1543_ = crate::leanh::lean_ctor_get(v_job_1542_, 0);
                v_kind_1544_ = crate::leanh::lean_ctor_get(v_job_1542_, 1);
                v_caption_1545_ = crate::leanh::lean_ctor_get(v_job_1542_, 2);
                v_optional_1546_ = crate::leanh::lean_ctor_get_uint8(
                    v_job_1542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_1547_ = lean_string_utf8_byte_size(v_caption_1545_);
                v___x_1548_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1549_ = lean_nat_dec_eq(v___x_1547_, v___x_1548_);
                if v___x_1549_ == 0 {
                    crate::leanh::lean_dec_ref(v_caption_1541_);
                    return v_job_1542_;
                } else {
                    crate::leanh::lean_inc(v_kind_1544_);
                    crate::leanh::lean_inc_ref(v_task_1543_);
                    v_isSharedCheck_1556_ = (!crate::leanh::lean_is_exclusive(v_job_1542_)) as u8;
                    if v_isSharedCheck_1556_ == 0 {
                        v_unused_1557_ = crate::leanh::lean_ctor_get(v_job_1542_, 2);
                        crate::leanh::lean_dec(v_unused_1557_);
                        v_unused_1558_ = crate::leanh::lean_ctor_get(v_job_1542_, 1);
                        crate::leanh::lean_dec(v_unused_1558_);
                        v_unused_1559_ = crate::leanh::lean_ctor_get(v_job_1542_, 0);
                        crate::leanh::lean_dec(v_unused_1559_);
                        v___x_1551_ = v_job_1542_;
                        v_isShared_1552_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_job_1542_);
                        v___x_1551_ = crate::leanh::lean_box(0);
                        v_isShared_1552_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1551_, 2, v_caption_1541_);
                    v___x_1554_ = v___x_1551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_task_1543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_kind_1544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_caption_1541_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1555_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1546_,
                    );
                    v___x_1554_ = v_reuseFailAlloc_1555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_setCaption_x3f(
    mut v_00_u03b1_1560_: *mut crate::leanh::LeanObject,
    mut v_caption_1561_: *mut crate::leanh::LeanObject,
    mut v_job_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1566_: u8 = 0;
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_unused_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1563_ = crate::leanh::lean_ctor_get(v_job_1562_, 0);
                v_kind_1564_ = crate::leanh::lean_ctor_get(v_job_1562_, 1);
                v_caption_1565_ = crate::leanh::lean_ctor_get(v_job_1562_, 2);
                v_optional_1566_ = crate::leanh::lean_ctor_get_uint8(
                    v_job_1562_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_1567_ = lean_string_utf8_byte_size(v_caption_1565_);
                v___x_1568_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1569_ = lean_nat_dec_eq(v___x_1567_, v___x_1568_);
                if v___x_1569_ == 0 {
                    crate::leanh::lean_dec_ref(v_caption_1561_);
                    return v_job_1562_;
                } else {
                    crate::leanh::lean_inc(v_kind_1564_);
                    crate::leanh::lean_inc_ref(v_task_1563_);
                    v_isSharedCheck_1576_ = (!crate::leanh::lean_is_exclusive(v_job_1562_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v_unused_1577_ = crate::leanh::lean_ctor_get(v_job_1562_, 2);
                        crate::leanh::lean_dec(v_unused_1577_);
                        v_unused_1578_ = crate::leanh::lean_ctor_get(v_job_1562_, 1);
                        crate::leanh::lean_dec(v_unused_1578_);
                        v_unused_1579_ = crate::leanh::lean_ctor_get(v_job_1562_, 0);
                        crate::leanh::lean_dec(v_unused_1579_);
                        v___x_1571_ = v_job_1562_;
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_job_1562_);
                        v___x_1571_ = crate::leanh::lean_box(0);
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1571_, 2, v_caption_1561_);
                    v___x_1574_ = v___x_1571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_task_1563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_kind_1564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_caption_1561_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1575_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1566_,
                    );
                    v___x_1574_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapResult___redArg(
    mut v_inst_1580_: *mut crate::leanh::LeanObject,
    mut v_f_1581_: *mut crate::leanh::LeanObject,
    mut v_self_1582_: *mut crate::leanh::LeanObject,
    mut v_prio_1583_: *mut crate::leanh::LeanObject,
    mut v_sync_1584_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1587_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_unused_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1585_ = crate::leanh::lean_ctor_get(v_self_1582_, 0);
                v_caption_1586_ = crate::leanh::lean_ctor_get(v_self_1582_, 2);
                v_optional_1587_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1582_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v_self_1582_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v_unused_1596_ = crate::leanh::lean_ctor_get(v_self_1582_, 1);
                    crate::leanh::lean_dec(v_unused_1596_);
                    v___x_1589_ = v_self_1582_;
                    v_isShared_1590_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1586_);
                    crate::leanh::lean_inc(v_task_1585_);
                    crate::leanh::lean_dec(v_self_1582_);
                    v___x_1589_ = crate::leanh::lean_box(0);
                    v_isShared_1590_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1591_ = lean_task_map(v_f_1581_, v_task_1585_, v_prio_1583_, v_sync_1584_);
                if v_isShared_1590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1589_, 1, v_inst_1580_);
                    crate::leanh::lean_ctor_set(v___x_1589_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1589_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_inst_1580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_caption_1586_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1594_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1587_,
                    );
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapResult___redArg___boxed(
    mut v_inst_1597_: *mut crate::leanh::LeanObject,
    mut v_f_1598_: *mut crate::leanh::LeanObject,
    mut v_self_1599_: *mut crate::leanh::LeanObject,
    mut v_prio_1600_: *mut crate::leanh::LeanObject,
    mut v_sync_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_1602_: u8 = 0;
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_1602_ = (crate::leanh::lean_unbox(v_sync_1601_) as u8);
    v_res_1603_ = l_Lake_Job_mapResult___redArg(
        v_inst_1597_,
        v_f_1598_,
        v_self_1599_,
        v_prio_1600_,
        v_sync_boxed_1602_,
    );
    return v_res_1603_;
}
pub unsafe fn l_Lake_Job_mapResult(
    mut v_00_u03b2_1604_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1605_: *mut crate::leanh::LeanObject,
    mut v_inst_1606_: *mut crate::leanh::LeanObject,
    mut v_f_1607_: *mut crate::leanh::LeanObject,
    mut v_self_1608_: *mut crate::leanh::LeanObject,
    mut v_prio_1609_: *mut crate::leanh::LeanObject,
    mut v_sync_1610_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1613_: u8 = 0;
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_unused_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1611_ = crate::leanh::lean_ctor_get(v_self_1608_, 0);
                v_caption_1612_ = crate::leanh::lean_ctor_get(v_self_1608_, 2);
                v_optional_1613_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1621_ = (!crate::leanh::lean_is_exclusive(v_self_1608_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v_unused_1622_ = crate::leanh::lean_ctor_get(v_self_1608_, 1);
                    crate::leanh::lean_dec(v_unused_1622_);
                    v___x_1615_ = v_self_1608_;
                    v_isShared_1616_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1612_);
                    crate::leanh::lean_inc(v_task_1611_);
                    crate::leanh::lean_dec(v_self_1608_);
                    v___x_1615_ = crate::leanh::lean_box(0);
                    v_isShared_1616_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1617_ = lean_task_map(v_f_1607_, v_task_1611_, v_prio_1609_, v_sync_1610_);
                if v_isShared_1616_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1615_, 1, v_inst_1606_);
                    crate::leanh::lean_ctor_set(v___x_1615_, 0, v___x_1617_);
                    v___x_1619_ = v___x_1615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_inst_1606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_caption_1612_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1620_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1613_,
                    );
                    v___x_1619_ = v_reuseFailAlloc_1620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapResult___boxed(
    mut v_00_u03b2_1623_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1624_: *mut crate::leanh::LeanObject,
    mut v_inst_1625_: *mut crate::leanh::LeanObject,
    mut v_f_1626_: *mut crate::leanh::LeanObject,
    mut v_self_1627_: *mut crate::leanh::LeanObject,
    mut v_prio_1628_: *mut crate::leanh::LeanObject,
    mut v_sync_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_1630_: u8 = 0;
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_1630_ = (crate::leanh::lean_unbox(v_sync_1629_) as u8);
    v_res_1631_ = l_Lake_Job_mapResult(
        v_00_u03b2_1623_,
        v_00_u03b1_1624_,
        v_inst_1625_,
        v_f_1626_,
        v_self_1627_,
        v_prio_1628_,
        v_sync_boxed_1630_,
    );
    return v_res_1631_;
}
pub unsafe fn l_Lake_Job_mapOk___redArg___lam__0(
    mut v_f_1632_: *mut crate::leanh::LeanObject,
    mut v_x_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1633_) == 0 {
                    v_a_1634_ = crate::leanh::lean_ctor_get(v_x_1633_, 0);
                    crate::leanh::lean_inc(v_a_1634_);
                    v_a_1635_ = crate::leanh::lean_ctor_get(v_x_1633_, 1);
                    crate::leanh::lean_inc(v_a_1635_);
                    crate::leanh::lean_dec_ref_known(v_x_1633_, 2);
                    v___x_1636_ = crate::leanh::lean_apply_2(v_f_1632_, v_a_1634_, v_a_1635_);
                    return v___x_1636_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_1632_);
                    v_a_1637_ = crate::leanh::lean_ctor_get(v_x_1633_, 0);
                    v_a_1638_ = crate::leanh::lean_ctor_get(v_x_1633_, 1);
                    v_isSharedCheck_1645_ = (!crate::leanh::lean_is_exclusive(v_x_1633_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1640_ = v_x_1633_;
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1638_);
                        crate::leanh::lean_inc(v_a_1637_);
                        crate::leanh::lean_dec(v_x_1633_);
                        v___x_1640_ = crate::leanh::lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1641_ == 0 {
                    v___x_1643_ = v___x_1640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_a_1638_);
                    v___x_1643_ = v_reuseFailAlloc_1644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapOk___redArg(
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_f_1647_: *mut crate::leanh::LeanObject,
    mut v_self_1648_: *mut crate::leanh::LeanObject,
    mut v_prio_1649_: *mut crate::leanh::LeanObject,
    mut v_sync_1650_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1653_: u8 = 0;
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___f_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut v_unused_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1651_ = crate::leanh::lean_ctor_get(v_self_1648_, 0);
                v_caption_1652_ = crate::leanh::lean_ctor_get(v_self_1648_, 2);
                v_optional_1653_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1662_ = (!crate::leanh::lean_is_exclusive(v_self_1648_)) as u8;
                if v_isSharedCheck_1662_ == 0 {
                    v_unused_1663_ = crate::leanh::lean_ctor_get(v_self_1648_, 1);
                    crate::leanh::lean_dec(v_unused_1663_);
                    v___x_1655_ = v_self_1648_;
                    v_isShared_1656_ = v_isSharedCheck_1662_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1652_);
                    crate::leanh::lean_inc(v_task_1651_);
                    crate::leanh::lean_dec(v_self_1648_);
                    v___x_1655_ = crate::leanh::lean_box(0);
                    v_isShared_1656_ = v_isSharedCheck_1662_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1657_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_mapOk___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1657_, 0, v_f_1647_);
                v___x_1658_ = lean_task_map(v___f_1657_, v_task_1651_, v_prio_1649_, v_sync_1650_);
                if v_isShared_1656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1655_, 1, v_inst_1646_);
                    crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1658_);
                    v___x_1660_ = v___x_1655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1661_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_inst_1646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_caption_1652_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1661_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1653_,
                    );
                    v___x_1660_ = v_reuseFailAlloc_1661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapOk___redArg___boxed(
    mut v_inst_1664_: *mut crate::leanh::LeanObject,
    mut v_f_1665_: *mut crate::leanh::LeanObject,
    mut v_self_1666_: *mut crate::leanh::LeanObject,
    mut v_prio_1667_: *mut crate::leanh::LeanObject,
    mut v_sync_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_1669_: u8 = 0;
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_1669_ = (crate::leanh::lean_unbox(v_sync_1668_) as u8);
    v_res_1670_ = l_Lake_Job_mapOk___redArg(
        v_inst_1664_,
        v_f_1665_,
        v_self_1666_,
        v_prio_1667_,
        v_sync_boxed_1669_,
    );
    return v_res_1670_;
}
pub unsafe fn l_Lake_Job_mapOk(
    mut v_00_u03b2_1671_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
    mut v_f_1674_: *mut crate::leanh::LeanObject,
    mut v_self_1675_: *mut crate::leanh::LeanObject,
    mut v_prio_1676_: *mut crate::leanh::LeanObject,
    mut v_sync_1677_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1680_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___f_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut v_unused_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1678_ = crate::leanh::lean_ctor_get(v_self_1675_, 0);
                v_caption_1679_ = crate::leanh::lean_ctor_get(v_self_1675_, 2);
                v_optional_1680_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1689_ = (!crate::leanh::lean_is_exclusive(v_self_1675_)) as u8;
                if v_isSharedCheck_1689_ == 0 {
                    v_unused_1690_ = crate::leanh::lean_ctor_get(v_self_1675_, 1);
                    crate::leanh::lean_dec(v_unused_1690_);
                    v___x_1682_ = v_self_1675_;
                    v_isShared_1683_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1679_);
                    crate::leanh::lean_inc(v_task_1678_);
                    crate::leanh::lean_dec(v_self_1675_);
                    v___x_1682_ = crate::leanh::lean_box(0);
                    v_isShared_1683_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1684_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_mapOk___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1684_, 0, v_f_1674_);
                v___x_1685_ = lean_task_map(v___f_1684_, v_task_1678_, v_prio_1676_, v_sync_1677_);
                if v_isShared_1683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1682_, 1, v_inst_1673_);
                    crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1685_);
                    v___x_1687_ = v___x_1682_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_inst_1673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_caption_1679_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1688_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1680_,
                    );
                    v___x_1687_ = v_reuseFailAlloc_1688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapOk___boxed(
    mut v_00_u03b2_1691_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1692_: *mut crate::leanh::LeanObject,
    mut v_inst_1693_: *mut crate::leanh::LeanObject,
    mut v_f_1694_: *mut crate::leanh::LeanObject,
    mut v_self_1695_: *mut crate::leanh::LeanObject,
    mut v_prio_1696_: *mut crate::leanh::LeanObject,
    mut v_sync_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_1698_: u8 = 0;
    let mut v_res_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_1698_ = (crate::leanh::lean_unbox(v_sync_1697_) as u8);
    v_res_1699_ = l_Lake_Job_mapOk(
        v_00_u03b2_1691_,
        v_00_u03b1_1692_,
        v_inst_1693_,
        v_f_1694_,
        v_self_1695_,
        v_prio_1696_,
        v_sync_boxed_1698_,
    );
    return v_res_1699_;
}
pub unsafe fn l_Lake_Job_map___redArg___lam__0(
    mut v_f_1700_: *mut crate::leanh::LeanObject,
    mut v_x_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_a_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1701_) == 0 {
                    v_a_1702_ = crate::leanh::lean_ctor_get(v_x_1701_, 0);
                    v_a_1703_ = crate::leanh::lean_ctor_get(v_x_1701_, 1);
                    v_isSharedCheck_1711_ = (!crate::leanh::lean_is_exclusive(v_x_1701_)) as u8;
                    if v_isSharedCheck_1711_ == 0 {
                        v___x_1705_ = v_x_1701_;
                        v_isShared_1706_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1703_);
                        crate::leanh::lean_inc(v_a_1702_);
                        crate::leanh::lean_dec(v_x_1701_);
                        v___x_1705_ = crate::leanh::lean_box(0);
                        v_isShared_1706_ = v_isSharedCheck_1711_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1700_);
                    v_a_1712_ = crate::leanh::lean_ctor_get(v_x_1701_, 0);
                    v_a_1713_ = crate::leanh::lean_ctor_get(v_x_1701_, 1);
                    v_isSharedCheck_1720_ = (!crate::leanh::lean_is_exclusive(v_x_1701_)) as u8;
                    if v_isSharedCheck_1720_ == 0 {
                        v___x_1715_ = v_x_1701_;
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1713_);
                        crate::leanh::lean_inc(v_a_1712_);
                        crate::leanh::lean_dec(v_x_1701_);
                        v___x_1715_ = crate::leanh::lean_box(0);
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1707_ = crate::leanh::lean_apply_1(v_f_1700_, v_a_1702_);
                if v_isShared_1706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1705_, 0, v___x_1707_);
                    v___x_1709_ = v___x_1705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_a_1703_);
                    v___x_1709_ = v_reuseFailAlloc_1710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1709_;
            }
            3 => {
                if v_isShared_1716_ == 0 {
                    v___x_1718_ = v___x_1715_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_a_1713_);
                    v___x_1718_ = v_reuseFailAlloc_1719_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_map___redArg(
    mut v_inst_1721_: *mut crate::leanh::LeanObject,
    mut v_f_1722_: *mut crate::leanh::LeanObject,
    mut v_self_1723_: *mut crate::leanh::LeanObject,
    mut v_prio_1724_: *mut crate::leanh::LeanObject,
    mut v_sync_1725_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1728_: u8 = 0;
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___f_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_unused_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1726_ = crate::leanh::lean_ctor_get(v_self_1723_, 0);
                v_caption_1727_ = crate::leanh::lean_ctor_get(v_self_1723_, 2);
                v_optional_1728_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1737_ = (!crate::leanh::lean_is_exclusive(v_self_1723_)) as u8;
                if v_isSharedCheck_1737_ == 0 {
                    v_unused_1738_ = crate::leanh::lean_ctor_get(v_self_1723_, 1);
                    crate::leanh::lean_dec(v_unused_1738_);
                    v___x_1730_ = v_self_1723_;
                    v_isShared_1731_ = v_isSharedCheck_1737_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1727_);
                    crate::leanh::lean_inc(v_task_1726_);
                    crate::leanh::lean_dec(v_self_1723_);
                    v___x_1730_ = crate::leanh::lean_box(0);
                    v_isShared_1731_ = v_isSharedCheck_1737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1732_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1732_, 0, v_f_1722_);
                v___x_1733_ = lean_task_map(v___f_1732_, v_task_1726_, v_prio_1724_, v_sync_1725_);
                if v_isShared_1731_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1730_, 1, v_inst_1721_);
                    crate::leanh::lean_ctor_set(v___x_1730_, 0, v___x_1733_);
                    v___x_1735_ = v___x_1730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_inst_1721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_caption_1727_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1736_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1728_,
                    );
                    v___x_1735_ = v_reuseFailAlloc_1736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_map___redArg___boxed(
    mut v_inst_1739_: *mut crate::leanh::LeanObject,
    mut v_f_1740_: *mut crate::leanh::LeanObject,
    mut v_self_1741_: *mut crate::leanh::LeanObject,
    mut v_prio_1742_: *mut crate::leanh::LeanObject,
    mut v_sync_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_1744_: u8 = 0;
    let mut v_res_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_1744_ = (crate::leanh::lean_unbox(v_sync_1743_) as u8);
    v_res_1745_ = l_Lake_Job_map___redArg(
        v_inst_1739_,
        v_f_1740_,
        v_self_1741_,
        v_prio_1742_,
        v_sync_boxed_1744_,
    );
    return v_res_1745_;
}
pub unsafe fn l_Lake_Job_map(
    mut v_00_u03b2_1746_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1747_: *mut crate::leanh::LeanObject,
    mut v_inst_1748_: *mut crate::leanh::LeanObject,
    mut v_f_1749_: *mut crate::leanh::LeanObject,
    mut v_self_1750_: *mut crate::leanh::LeanObject,
    mut v_prio_1751_: *mut crate::leanh::LeanObject,
    mut v_sync_1752_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1755_: u8 = 0;
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___f_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1764_: u8 = 0;
    let mut v_unused_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1753_ = crate::leanh::lean_ctor_get(v_self_1750_, 0);
                v_caption_1754_ = crate::leanh::lean_ctor_get(v_self_1750_, 2);
                v_optional_1755_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1750_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1764_ = (!crate::leanh::lean_is_exclusive(v_self_1750_)) as u8;
                if v_isSharedCheck_1764_ == 0 {
                    v_unused_1765_ = crate::leanh::lean_ctor_get(v_self_1750_, 1);
                    crate::leanh::lean_dec(v_unused_1765_);
                    v___x_1757_ = v_self_1750_;
                    v_isShared_1758_ = v_isSharedCheck_1764_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1754_);
                    crate::leanh::lean_inc(v_task_1753_);
                    crate::leanh::lean_dec(v_self_1750_);
                    v___x_1757_ = crate::leanh::lean_box(0);
                    v_isShared_1758_ = v_isSharedCheck_1764_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1759_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1759_, 0, v_f_1749_);
                v___x_1760_ = lean_task_map(v___f_1759_, v_task_1753_, v_prio_1751_, v_sync_1752_);
                if v_isShared_1758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1757_, 1, v_inst_1748_);
                    crate::leanh::lean_ctor_set(v___x_1757_, 0, v___x_1760_);
                    v___x_1762_ = v___x_1757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_inst_1748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_caption_1754_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1755_,
                    );
                    v___x_1762_ = v_reuseFailAlloc_1763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_map___boxed(
    mut v_00_u03b2_1766_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1767_: *mut crate::leanh::LeanObject,
    mut v_inst_1768_: *mut crate::leanh::LeanObject,
    mut v_f_1769_: *mut crate::leanh::LeanObject,
    mut v_self_1770_: *mut crate::leanh::LeanObject,
    mut v_prio_1771_: *mut crate::leanh::LeanObject,
    mut v_sync_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_1773_: u8 = 0;
    let mut v_res_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_1773_ = (crate::leanh::lean_unbox(v_sync_1772_) as u8);
    v_res_1774_ = l_Lake_Job_map(
        v_00_u03b2_1766_,
        v_00_u03b1_1767_,
        v_inst_1768_,
        v_f_1769_,
        v_self_1770_,
        v_prio_1771_,
        v_sync_boxed_1773_,
    );
    return v_res_1774_;
}
pub unsafe fn l_Lake_Job_instFunctor___lam__1(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1776_: *mut crate::leanh::LeanObject,
    mut v_f_1777_: *mut crate::leanh::LeanObject,
    mut v_self_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1781_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___f_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_unused_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1779_ = crate::leanh::lean_ctor_get(v_self_1778_, 0);
                v_caption_1780_ = crate::leanh::lean_ctor_get(v_self_1778_, 2);
                v_optional_1781_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_1778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1793_ = (!crate::leanh::lean_is_exclusive(v_self_1778_)) as u8;
                if v_isSharedCheck_1793_ == 0 {
                    v_unused_1794_ = crate::leanh::lean_ctor_get(v_self_1778_, 1);
                    crate::leanh::lean_dec(v_unused_1794_);
                    v___x_1783_ = v_self_1778_;
                    v_isShared_1784_ = v_isSharedCheck_1793_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1780_);
                    crate::leanh::lean_inc(v_task_1779_);
                    crate::leanh::lean_dec(v_self_1778_);
                    v___x_1783_ = crate::leanh::lean_box(0);
                    v_isShared_1784_ = v_isSharedCheck_1793_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1785_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_map___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1785_, 0, v_f_1777_);
                v___x_1786_ = crate::leanh::lean_box(0);
                v___x_1787_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1788_ = 0;
                v___x_1789_ = lean_task_map(v___f_1785_, v_task_1779_, v___x_1787_, v___x_1788_);
                if v_isShared_1784_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1783_, 1, v___x_1786_);
                    crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1789_);
                    v___x_1791_ = v___x_1783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_caption_1780_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1781_,
                    );
                    v___x_1791_ = v_reuseFailAlloc_1792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_instFunctor___lam__0(
    mut v___f_1795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1796_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1800_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1800_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1800_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1800_, 2, v___y_1798_);
    v___x_1801_ = crate::leanh::lean_apply_4(
        v___f_1795_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1800_,
        v___y_1799_,
    );
    return v___x_1801_;
}
pub unsafe fn l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(
    mut v_self_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1809_);
    return v_self_1809_;
}
pub unsafe fn l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg___boxed(
    mut v_self_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ =
        l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___redArg(v_self_1810_);
    crate::leanh::lean_dec_ref(v_self_1810_);
    return v_res_1811_;
}
pub unsafe fn l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(
    mut v_00_u03b1_1812_: *mut crate::leanh::LeanObject,
    mut v_self_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1813_);
    return v_self_1813_;
}
pub unsafe fn l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl___boxed(
    mut v_00_u03b1_1814_: *mut crate::leanh::LeanObject,
    mut v_self_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1816_ = l___private_Lake_Build_Job_Basic_0__Lake_JobTask_toOpaqueImpl(
        v_00_u03b1_1814_,
        v_self_1815_,
    );
    crate::leanh::lean_dec_ref(v_self_1815_);
    return v_res_1816_;
}
pub unsafe fn l_Lake_instCoeOutJobTaskOpaqueJobTask(
    mut v_00_u03b1_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = l_Lake_instCoeOutJobTaskOpaqueJobTask___closed__0;
    return v___x_1819_;
}
pub unsafe fn l_Lake_Job_toOpaque___redArg(
    mut v_job_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_1823_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut v_unused_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_1821_ = crate::leanh::lean_ctor_get(v_job_1820_, 0);
                v_caption_1822_ = crate::leanh::lean_ctor_get(v_job_1820_, 2);
                v_optional_1823_ = crate::leanh::lean_ctor_get_uint8(
                    v_job_1820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1831_ = (!crate::leanh::lean_is_exclusive(v_job_1820_)) as u8;
                if v_isSharedCheck_1831_ == 0 {
                    v_unused_1832_ = crate::leanh::lean_ctor_get(v_job_1820_, 1);
                    crate::leanh::lean_dec(v_unused_1832_);
                    v___x_1825_ = v_job_1820_;
                    v_isShared_1826_ = v_isSharedCheck_1831_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_1822_);
                    crate::leanh::lean_inc(v_task_1821_);
                    crate::leanh::lean_dec(v_job_1820_);
                    v___x_1825_ = crate::leanh::lean_box(0);
                    v_isShared_1826_ = v_isSharedCheck_1831_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1827_ = crate::leanh::lean_box(0);
                if v_isShared_1826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1825_, 1, v___x_1827_);
                    v___x_1829_ = v___x_1825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_task_1821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_caption_1822_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1830_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_1823_,
                    );
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_toOpaque(
    mut v_00_u03b1_1833_: *mut crate::leanh::LeanObject,
    mut v_job_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lake_Job_toOpaque___redArg(v_job_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lake_instCoeOutJobOpaqueJob(
    mut v_00_u03b1_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lake_instCoeOutJobOpaqueJob___closed__0;
    return v___x_1838_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Job_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Trace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedJobAction_default = _init_l_Lake_instInhabitedJobAction_default();
    l_Lake_instInhabitedJobAction = _init_l_Lake_instInhabitedJobAction();
    l_Lake_JobAction_instLT = _init_l_Lake_JobAction_instLT();
    crate::leanh::lean_mark_persistent(l_Lake_JobAction_instLT);
    l_Lake_JobAction_instLE = _init_l_Lake_JobAction_instLE();
    crate::leanh::lean_mark_persistent(l_Lake_JobAction_instLE);
    l_Lake_instInhabitedJobState_default = _init_l_Lake_instInhabitedJobState_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedJobState_default);
    l_Lake_instInhabitedJobState = _init_l_Lake_instInhabitedJobState();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedJobState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Job_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Job_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Opaque(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Trace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Job_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Job_Basic(builtin);
}
