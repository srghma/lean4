// Lean compiler output
// Module: Init.Data.Format.Syntax
// Imports: Init.Data.ToString.Name Init.Data.ToString.Basic Init.Data.Format.Instances Init.Data.Format.Macro
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Instances::{
    initialize_Init_Data_Format_Instances, runtime_initialize_Init_Data_Format_Instances,
};
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_replacePrefix;
use crate::r#gen::Init::Prelude::l_Function_comp;
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_utf8_extract;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_array_get_size, lean_array_to_list, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
};
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value:
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
    m_data: [58, 0],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [33, 58, 0],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_formatStxAux___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_formatStxAux___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_formatStxAux___closed__4_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [93, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__6_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [60, 109, 105, 115, 115, 105, 110, 103, 62, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__8_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [46, 46, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__10_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__10_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__13_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__12_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Syntax_formatStxAux___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__12_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Syntax_formatStxAux___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__14_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__13_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__15_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [40, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_formatStxAux___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_formatStxAux___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_formatStxAux___closed__19_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__16_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__20_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__21_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__22_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Syntax_formatStxAux___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__23_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instToFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToFormat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instToFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instToString___closed__1_value: crate::leanh::LeanClosureObject<5> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_comp as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_instToString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instToFormatTSyntax___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToFormatTSyntax___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToFormatTSyntax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormatTSyntax___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instToStringTSyntax___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToStringTSyntax___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToStringTSyntax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToStringTSyntax___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
    mut v_showInfo_296_: u8,
    mut v_info_297_: *mut crate::leanh::LeanObject,
    mut v_f_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_showInfo_296_ == 1 {
        match crate::leanh::lean_obj_tag(v_info_297_) {
            0 => {
                let mut v_leading_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pos_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_trailing_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_stopPos_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_stopPos_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_leading_299_ = crate::leanh::lean_ctor_get(v_info_297_, 0);
                crate::leanh::lean_inc_ref(v_leading_299_);
                v_pos_300_ = crate::leanh::lean_ctor_get(v_info_297_, 1);
                crate::leanh::lean_inc(v_pos_300_);
                v_trailing_301_ = crate::leanh::lean_ctor_get(v_info_297_, 2);
                crate::leanh::lean_inc_ref(v_trailing_301_);
                v_endPos_302_ = crate::leanh::lean_ctor_get(v_info_297_, 3);
                crate::leanh::lean_inc(v_endPos_302_);
                crate::leanh::lean_dec_ref_known(v_info_297_, 4);
                v_str_303_ = crate::leanh::lean_ctor_get(v_leading_299_, 0);
                crate::leanh::lean_inc_ref(v_str_303_);
                v_startPos_304_ = crate::leanh::lean_ctor_get(v_leading_299_, 1);
                crate::leanh::lean_inc(v_startPos_304_);
                v_stopPos_305_ = crate::leanh::lean_ctor_get(v_leading_299_, 2);
                crate::leanh::lean_inc(v_stopPos_305_);
                crate::leanh::lean_dec_ref(v_leading_299_);
                v___x_306_ = lean_string_utf8_extract(v_str_303_, v_startPos_304_, v_stopPos_305_);
                crate::leanh::lean_dec(v_stopPos_305_);
                crate::leanh::lean_dec(v_startPos_304_);
                crate::leanh::lean_dec_ref(v_str_303_);
                v___x_307_ = l_String_quote(v___x_306_);
                v___x_308_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_308_, 0, v___x_307_);
                v___x_309_ =
                    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                v___x_310_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_310_, 0, v___x_308_);
                crate::leanh::lean_ctor_set(v___x_310_, 1, v___x_309_);
                v_str_311_ = crate::leanh::lean_ctor_get(v_trailing_301_, 0);
                crate::leanh::lean_inc_ref(v_str_311_);
                v_startPos_312_ = crate::leanh::lean_ctor_get(v_trailing_301_, 1);
                crate::leanh::lean_inc(v_startPos_312_);
                v_stopPos_313_ = crate::leanh::lean_ctor_get(v_trailing_301_, 2);
                crate::leanh::lean_inc(v_stopPos_313_);
                crate::leanh::lean_dec_ref(v_trailing_301_);
                v___x_314_ = l_Nat_reprFast(v_pos_300_);
                v___x_315_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
                v___x_316_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_316_, 0, v___x_310_);
                crate::leanh::lean_ctor_set(v___x_316_, 1, v___x_315_);
                v___x_317_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_317_, 0, v___x_316_);
                crate::leanh::lean_ctor_set(v___x_317_, 1, v___x_309_);
                v___x_318_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
                crate::leanh::lean_ctor_set(v___x_318_, 1, v_f_298_);
                v___x_319_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_319_, 0, v___x_318_);
                crate::leanh::lean_ctor_set(v___x_319_, 1, v___x_309_);
                v___x_320_ = l_Nat_reprFast(v_endPos_302_);
                v___x_321_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_321_, 0, v___x_320_);
                v___x_322_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_319_);
                crate::leanh::lean_ctor_set(v___x_322_, 1, v___x_321_);
                v___x_323_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_323_, 0, v___x_322_);
                crate::leanh::lean_ctor_set(v___x_323_, 1, v___x_309_);
                v___x_324_ = lean_string_utf8_extract(v_str_311_, v_startPos_312_, v_stopPos_313_);
                crate::leanh::lean_dec(v_stopPos_313_);
                crate::leanh::lean_dec(v_startPos_312_);
                crate::leanh::lean_dec_ref(v_str_311_);
                v___x_325_ = l_String_quote(v___x_324_);
                v___x_326_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
                v___x_327_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_327_, 0, v___x_323_);
                crate::leanh::lean_ctor_set(v___x_327_, 1, v___x_326_);
                return v___x_327_;
            }
            1 => {
                let mut v_canonical_328_: u8 = 0;
                v_canonical_328_ = crate::leanh::lean_ctor_get_uint8(
                    v_info_297_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_canonical_328_ == 0 {
                    let mut v_pos_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_endPos_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_pos_329_ = crate::leanh::lean_ctor_get(v_info_297_, 0);
                    crate::leanh::lean_inc(v_pos_329_);
                    v_endPos_330_ = crate::leanh::lean_ctor_get(v_info_297_, 1);
                    crate::leanh::lean_inc(v_endPos_330_);
                    crate::leanh::lean_dec_ref_known(v_info_297_, 2);
                    v___x_331_ = l_Nat_reprFast(v_pos_329_);
                    v___x_332_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_332_, 0, v___x_331_);
                    v___x_333_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                    v___x_334_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_334_, 0, v___x_332_);
                    crate::leanh::lean_ctor_set(v___x_334_, 1, v___x_333_);
                    v___x_335_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_335_, 0, v___x_334_);
                    crate::leanh::lean_ctor_set(v___x_335_, 1, v_f_298_);
                    v___x_336_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_336_, 0, v___x_335_);
                    crate::leanh::lean_ctor_set(v___x_336_, 1, v___x_333_);
                    v___x_337_ = l_Nat_reprFast(v_endPos_330_);
                    v___x_338_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_338_, 0, v___x_337_);
                    v___x_339_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_339_, 0, v___x_336_);
                    crate::leanh::lean_ctor_set(v___x_339_, 1, v___x_338_);
                    return v___x_339_;
                } else {
                    let mut v_pos_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_endPos_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_pos_340_ = crate::leanh::lean_ctor_get(v_info_297_, 0);
                    crate::leanh::lean_inc(v_pos_340_);
                    v_endPos_341_ = crate::leanh::lean_ctor_get(v_info_297_, 1);
                    crate::leanh::lean_inc(v_endPos_341_);
                    crate::leanh::lean_dec_ref_known(v_info_297_, 2);
                    v___x_342_ = l_Nat_reprFast(v_pos_340_);
                    v___x_343_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_343_, 0, v___x_342_);
                    v___x_344_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3;
                    v___x_345_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_345_, 0, v___x_343_);
                    crate::leanh::lean_ctor_set(v___x_345_, 1, v___x_344_);
                    v___x_346_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_346_, 0, v___x_345_);
                    crate::leanh::lean_ctor_set(v___x_346_, 1, v_f_298_);
                    v___x_347_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                    v___x_348_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_348_, 0, v___x_346_);
                    crate::leanh::lean_ctor_set(v___x_348_, 1, v___x_347_);
                    v___x_349_ = l_Nat_reprFast(v_endPos_341_);
                    v___x_350_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_350_, 0, v___x_349_);
                    v___x_351_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_351_, 0, v___x_348_);
                    crate::leanh::lean_ctor_set(v___x_351_, 1, v___x_350_);
                    return v___x_351_;
                }
            }
            _ => {
                crate::leanh::lean_dec(v_info_297_);
                return v_f_298_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_info_297_);
        return v_f_298_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(
    mut v_showInfo_352_: *mut crate::leanh::LeanObject,
    mut v_info_353_: *mut crate::leanh::LeanObject,
    mut v_f_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_showInfo_boxed_355_: u8 = 0;
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_355_ = (crate::leanh::lean_unbox(v_showInfo_352_) as u8);
    v_res_356_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
        v_showInfo_boxed_355_,
        v_info_353_,
        v_f_354_,
    );
    return v_res_356_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Syntax_formatStxAux_spec__0(
    mut v_a_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_nat_to_int(v_a_357_);
    return v___x_358_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(
    mut v_x_359_: *mut crate::leanh::LeanObject,
    mut v_x_360_: *mut crate::leanh::LeanObject,
    mut v_x_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_361_) == 0 {
                    crate::leanh::lean_dec(v_x_359_);
                    return v_x_360_;
                } else {
                    v_head_362_ = crate::leanh::lean_ctor_get(v_x_361_, 0);
                    v_tail_363_ = crate::leanh::lean_ctor_get(v_x_361_, 1);
                    v_isSharedCheck_372_ = (!crate::leanh::lean_is_exclusive(v_x_361_)) as u8;
                    if v_isSharedCheck_372_ == 0 {
                        v___x_365_ = v_x_361_;
                        v_isShared_366_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_363_);
                        crate::leanh::lean_inc(v_head_362_);
                        crate::leanh::lean_dec(v_x_361_);
                        v___x_365_ = crate::leanh::lean_box(0);
                        v_isShared_366_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_359_);
                if v_isShared_366_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_365_, 5);
                    crate::leanh::lean_ctor_set(v___x_365_, 1, v_x_359_);
                    crate::leanh::lean_ctor_set(v___x_365_, 0, v_x_360_);
                    v___x_368_ = v___x_365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_371_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_371_, 0, v_x_360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_371_, 1, v_x_359_);
                    v___x_368_ = v_reuseFailAlloc_371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_369_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_369_, 0, v___x_368_);
                crate::leanh::lean_ctor_set(v___x_369_, 1, v_head_362_);
                v_x_360_ = v___x_369_;
                v_x_361_ = v_tail_363_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
    mut v_x_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_373_) == 0 {
        let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_374_);
        v___x_375_ = crate::leanh::lean_box(0);
        return v___x_375_;
    } else {
        let mut v_tail_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_376_ = crate::leanh::lean_ctor_get(v_x_373_, 1);
        if crate::leanh::lean_obj_tag(v_tail_376_) == 0 {
            let mut v_head_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_374_);
            v_head_377_ = crate::leanh::lean_ctor_get(v_x_373_, 0);
            crate::leanh::lean_inc(v_head_377_);
            crate::leanh::lean_dec_ref_known(v_x_373_, 2);
            return v_head_377_;
        } else {
            let mut v_head_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_376_);
            v_head_378_ = crate::leanh::lean_ctor_get(v_x_373_, 0);
            crate::leanh::lean_inc(v_head_378_);
            crate::leanh::lean_dec_ref_known(v_x_373_, 2);
            v___x_379_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(v_x_374_, v_head_378_, v_tail_376_);
            return v___x_379_;
        }
    }
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = l_Lean_Syntax_formatStxAux___closed__0;
    v___x_382_ = lean_string_length(v___x_381_);
    return v___x_382_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__2_once),
        _init_l_Lean_Syntax_formatStxAux___closed__2,
    );
    v___x_384_ = lean_nat_to_int(v___x_383_);
    return v___x_384_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Syntax_formatStxAux___closed__15;
    v___x_406_ = lean_string_length(v___x_405_);
    return v___x_406_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__17_once),
        _init_l_Lean_Syntax_formatStxAux___closed__17,
    );
    v___x_408_ = lean_nat_to_int(v___x_407_);
    return v___x_408_;
}
pub unsafe fn l_Lean_Syntax_formatStxAux(
    mut v_maxDepth_420_: *mut crate::leanh::LeanObject,
    mut v_showInfo_421_: u8,
    mut v_depth_422_: *mut crate::leanh::LeanObject,
    mut v_x_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_441_: u8 = 0;
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shorterName_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_header_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_474_: u8 = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    let mut v_val_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v_val_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_423_) {
                0 => {
                    crate::leanh::lean_dec(v_maxDepth_420_);
                    v___x_434_ = l_Lean_Syntax_formatStxAux___closed__7;
                    return v___x_434_;
                }
                1 => {
                    v_info_435_ = crate::leanh::lean_ctor_get(v_x_423_, 0);
                    crate::leanh::lean_inc(v_info_435_);
                    v_kind_436_ = crate::leanh::lean_ctor_get(v_x_423_, 1);
                    crate::leanh::lean_inc(v_kind_436_);
                    v_args_437_ = crate::leanh::lean_ctor_get(v_x_423_, 2);
                    crate::leanh::lean_inc_ref(v_args_437_);
                    crate::leanh::lean_dec_ref_known(v_x_423_, 3);
                    v___x_438_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_depth_439_ = lean_nat_add(v_depth_422_, v___x_438_);
                    v___x_451_ = l_Lean_Syntax_formatStxAux___closed__11;
                    v___x_452_ = lean_name_eq(v_kind_436_, v___x_451_);
                    if v___x_452_ == 0 {
                        v___x_453_ = l_Lean_Syntax_formatStxAux___closed__14;
                        v___x_454_ = crate::leanh::lean_box(0);
                        v_shorterName_455_ =
                            l_Lean_Name_replacePrefix(v_kind_436_, v___x_453_, v___x_454_);
                        v___x_456_ = 1;
                        v___x_457_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_shorterName_455_,
                                v___x_456_,
                            );
                        v___x_458_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_458_, 0, v___x_457_);
                        v_header_459_ =
                            l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                                v_showInfo_421_,
                                v_info_435_,
                                v___x_458_,
                            );
                        v___x_482_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_483_ = lean_array_get_size(v_args_437_);
                        v___x_484_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
                        if v___x_484_ == 0 {
                            v___y_474_ = v___x_484_;
                            state = 5;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v_maxDepth_420_) == 0 {
                                crate::leanh::lean_inc(v_depth_439_);
                                v___y_480_ = v_depth_439_;
                                state = 6;
                                continue;
                            } else {
                                v_val_485_ = crate::leanh::lean_ctor_get(v_maxDepth_420_, 0);
                                crate::leanh::lean_inc(v_val_485_);
                                v___y_480_ = v_val_485_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_kind_436_);
                        crate::leanh::lean_dec(v_info_435_);
                        v___x_486_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_487_ = lean_array_get_size(v_args_437_);
                        v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
                        if v___x_488_ == 0 {
                            v___y_441_ = v___x_488_;
                            state = 2;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v_maxDepth_420_) == 0 {
                                crate::leanh::lean_inc(v_depth_439_);
                                v___y_449_ = v_depth_439_;
                                state = 3;
                                continue;
                            } else {
                                v_val_489_ = crate::leanh::lean_ctor_get(v_maxDepth_420_, 0);
                                crate::leanh::lean_inc(v_val_489_);
                                v___y_449_ = v_val_489_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
                2 => {
                    crate::leanh::lean_dec(v_maxDepth_420_);
                    v_info_490_ = crate::leanh::lean_ctor_get(v_x_423_, 0);
                    crate::leanh::lean_inc(v_info_490_);
                    v_val_491_ = crate::leanh::lean_ctor_get(v_x_423_, 1);
                    crate::leanh::lean_inc_ref(v_val_491_);
                    crate::leanh::lean_dec_ref_known(v_x_423_, 2);
                    v___x_492_ = l_String_quote(v_val_491_);
                    v___x_493_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_493_, 0, v___x_492_);
                    v___x_494_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                        v_showInfo_421_,
                        v_info_490_,
                        v___x_493_,
                    );
                    return v___x_494_;
                }
                _ => {
                    crate::leanh::lean_dec(v_maxDepth_420_);
                    v_info_495_ = crate::leanh::lean_ctor_get(v_x_423_, 0);
                    crate::leanh::lean_inc(v_info_495_);
                    v_val_496_ = crate::leanh::lean_ctor_get(v_x_423_, 2);
                    crate::leanh::lean_inc(v_val_496_);
                    crate::leanh::lean_dec_ref_known(v_x_423_, 4);
                    v___x_497_ = l_Lean_Syntax_formatStxAux___closed__23;
                    v___x_498_ = 1;
                    v___x_499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_val_496_, v___x_498_,
                    );
                    v___x_500_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_500_, 0, v___x_499_);
                    v___x_501_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_501_, 0, v___x_497_);
                    crate::leanh::lean_ctor_set(v___x_501_, 1, v___x_500_);
                    v___x_502_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                        v_showInfo_421_,
                        v_info_495_,
                        v___x_501_,
                    );
                    return v___x_502_;
                }
            },
            1 => {
                v___x_426_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__3_once),
                    _init_l_Lean_Syntax_formatStxAux___closed__3,
                );
                v___x_427_ = l_Lean_Syntax_formatStxAux___closed__4;
                v___x_428_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_428_, 0, v___x_427_);
                crate::leanh::lean_ctor_set(v___x_428_, 1, v___y_425_);
                v___x_429_ = l_Lean_Syntax_formatStxAux___closed__5;
                v___x_430_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_430_, 0, v___x_428_);
                crate::leanh::lean_ctor_set(v___x_430_, 1, v___x_429_);
                v___x_431_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_431_, 0, v___x_426_);
                crate::leanh::lean_ctor_set(v___x_431_, 1, v___x_430_);
                v___x_432_ = 0;
                v___x_433_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_433_, 0, v___x_431_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_433_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_432_,
                );
                return v___x_433_;
            }
            2 => {
                if v___y_441_ == 0 {
                    v___x_442_ = lean_array_to_list(v_args_437_);
                    v___x_443_ = crate::leanh::lean_box(0);
                    v___x_444_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
                        v_maxDepth_420_,
                        v_showInfo_421_,
                        v_depth_439_,
                        v___x_442_,
                        v___x_443_,
                    );
                    crate::leanh::lean_dec(v_depth_439_);
                    v___x_445_ = crate::leanh::lean_box(1);
                    v___x_446_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
                        v___x_444_, v___x_445_,
                    );
                    v___y_425_ = v___x_446_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_depth_439_);
                    crate::leanh::lean_dec_ref(v_args_437_);
                    crate::leanh::lean_dec(v_maxDepth_420_);
                    v___x_447_ = l_Lean_Syntax_formatStxAux___closed__9;
                    v___y_425_ = v___x_447_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_450_ = lean_nat_dec_lt(v___y_449_, v_depth_439_);
                crate::leanh::lean_dec(v___y_449_);
                v___y_441_ = v___x_450_;
                state = 2;
                continue;
            }
            4 => {
                v___x_462_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_462_, 0, v_header_459_);
                crate::leanh::lean_ctor_set(v___x_462_, 1, v___y_461_);
                v___x_463_ = crate::leanh::lean_box(1);
                v___x_464_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
                    v___x_462_, v___x_463_,
                );
                v___x_465_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__18_once),
                    _init_l_Lean_Syntax_formatStxAux___closed__18,
                );
                v___x_466_ = l_Lean_Syntax_formatStxAux___closed__19;
                v___x_467_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_467_, 0, v___x_466_);
                crate::leanh::lean_ctor_set(v___x_467_, 1, v___x_464_);
                v___x_468_ = l_Lean_Syntax_formatStxAux___closed__20;
                v___x_469_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_469_, 0, v___x_467_);
                crate::leanh::lean_ctor_set(v___x_469_, 1, v___x_468_);
                v___x_470_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_470_, 0, v___x_465_);
                crate::leanh::lean_ctor_set(v___x_470_, 1, v___x_469_);
                v___x_471_ = 0;
                v___x_472_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_472_, 0, v___x_470_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_472_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_471_,
                );
                return v___x_472_;
            }
            5 => {
                if v___y_474_ == 0 {
                    v___x_475_ = lean_array_to_list(v_args_437_);
                    v___x_476_ = crate::leanh::lean_box(0);
                    v___x_477_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
                        v_maxDepth_420_,
                        v_showInfo_421_,
                        v_depth_439_,
                        v___x_475_,
                        v___x_476_,
                    );
                    crate::leanh::lean_dec(v_depth_439_);
                    v___y_461_ = v___x_477_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_depth_439_);
                    crate::leanh::lean_dec_ref(v_args_437_);
                    crate::leanh::lean_dec(v_maxDepth_420_);
                    v___x_478_ = l_Lean_Syntax_formatStxAux___closed__21;
                    v___y_461_ = v___x_478_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_481_ = lean_nat_dec_lt(v___y_480_, v_depth_439_);
                crate::leanh::lean_dec(v___y_480_);
                v___y_474_ = v___x_481_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
    mut v_maxDepth_503_: *mut crate::leanh::LeanObject,
    mut v_showInfo_504_: u8,
    mut v_depth_505_: *mut crate::leanh::LeanObject,
    mut v_a_506_: *mut crate::leanh::LeanObject,
    mut v_a_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_506_) == 0 {
                    crate::leanh::lean_dec(v_maxDepth_503_);
                    v___x_508_ = l_List_reverse___redArg(v_a_507_);
                    return v___x_508_;
                } else {
                    v_head_509_ = crate::leanh::lean_ctor_get(v_a_506_, 0);
                    v_tail_510_ = crate::leanh::lean_ctor_get(v_a_506_, 1);
                    v_isSharedCheck_519_ = (!crate::leanh::lean_is_exclusive(v_a_506_)) as u8;
                    if v_isSharedCheck_519_ == 0 {
                        v___x_512_ = v_a_506_;
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_510_);
                        crate::leanh::lean_inc(v_head_509_);
                        crate::leanh::lean_dec(v_a_506_);
                        v___x_512_ = crate::leanh::lean_box(0);
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_maxDepth_503_);
                v___x_514_ = l_Lean_Syntax_formatStxAux(
                    v_maxDepth_503_,
                    v_showInfo_504_,
                    v_depth_505_,
                    v_head_509_,
                );
                if v_isShared_513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_512_, 1, v_a_507_);
                    crate::leanh::lean_ctor_set(v___x_512_, 0, v___x_514_);
                    v___x_516_ = v___x_512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_507_);
                    v___x_516_ = v_reuseFailAlloc_518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_506_ = v_tail_510_;
                v_a_507_ = v___x_516_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1___boxed(
    mut v_maxDepth_520_: *mut crate::leanh::LeanObject,
    mut v_showInfo_521_: *mut crate::leanh::LeanObject,
    mut v_depth_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
    mut v_a_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_showInfo_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_525_ = (crate::leanh::lean_unbox(v_showInfo_521_) as u8);
    v_res_526_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
        v_maxDepth_520_,
        v_showInfo_boxed_525_,
        v_depth_522_,
        v_a_523_,
        v_a_524_,
    );
    crate::leanh::lean_dec(v_depth_522_);
    return v_res_526_;
}
pub unsafe fn l_Lean_Syntax_formatStxAux___boxed(
    mut v_maxDepth_527_: *mut crate::leanh::LeanObject,
    mut v_showInfo_528_: *mut crate::leanh::LeanObject,
    mut v_depth_529_: *mut crate::leanh::LeanObject,
    mut v_x_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_showInfo_boxed_531_: u8 = 0;
    let mut v_res_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_531_ = (crate::leanh::lean_unbox(v_showInfo_528_) as u8);
    v_res_532_ = l_Lean_Syntax_formatStxAux(
        v_maxDepth_527_,
        v_showInfo_boxed_531_,
        v_depth_529_,
        v_x_530_,
    );
    crate::leanh::lean_dec(v_depth_529_);
    return v_res_532_;
}
pub unsafe fn l_Lean_Syntax_formatStx(
    mut v_stx_533_: *mut crate::leanh::LeanObject,
    mut v_maxDepth_534_: *mut crate::leanh::LeanObject,
    mut v_showInfo_535_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_537_ =
        l_Lean_Syntax_formatStxAux(v_maxDepth_534_, v_showInfo_535_, v___x_536_, v_stx_533_);
    return v___x_537_;
}
pub unsafe fn l_Lean_Syntax_formatStx___boxed(
    mut v_stx_538_: *mut crate::leanh::LeanObject,
    mut v_maxDepth_539_: *mut crate::leanh::LeanObject,
    mut v_showInfo_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_showInfo_boxed_541_: u8 = 0;
    let mut v_res_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_541_ = (crate::leanh::lean_unbox(v_showInfo_540_) as u8);
    v_res_542_ = l_Lean_Syntax_formatStx(v_stx_538_, v_maxDepth_539_, v_showInfo_boxed_541_);
    return v_res_542_;
}
pub unsafe fn l_Lean_Syntax_instToFormat___lam__0(
    mut v_stx_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = crate::leanh::lean_box(0);
    v___x_545_ = 0;
    v___x_546_ = l_Lean_Syntax_formatStx(v_stx_543_, v___x_544_, v___x_545_);
    return v___x_546_;
}
pub unsafe fn l_Lean_Syntax_instToString___lam__0(
    mut v_f_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Std_Format_defWidth;
    v___x_551_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_552_ = l_Std_Format_pretty(v_f_549_, v___x_550_, v___x_551_, v___x_551_);
    return v___x_552_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax___lam__0(
    mut v_x_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_559_ = crate::leanh::lean_box(0);
    v___x_560_ = 0;
    v___x_561_ = l_Lean_Syntax_formatStx(v_x_558_, v___x_559_, v___x_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax(
    mut v_k_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_564_ = l_Lean_Syntax_instToFormatTSyntax___closed__0;
    return v___f_564_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax___boxed(
    mut v_k_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Lean_Syntax_instToFormatTSyntax(v_k_565_);
    crate::leanh::lean_dec(v_k_565_);
    return v_res_566_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax___lam__0(
    mut v_x_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = crate::leanh::lean_box(0);
    v___x_569_ = 0;
    v___x_570_ = l_Lean_Syntax_formatStx(v_x_567_, v___x_568_, v___x_569_);
    v___x_571_ = l_Std_Format_defWidth;
    v___x_572_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_573_ = l_Std_Format_pretty(v___x_570_, v___x_571_, v___x_572_, v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax(
    mut v_k_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_576_ = l_Lean_Syntax_instToStringTSyntax___closed__0;
    return v___f_576_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax___boxed(
    mut v_k_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Syntax_instToStringTSyntax(v_k_577_);
    crate::leanh::lean_dec(v_k_577_);
    return v_res_578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Format_Syntax(builtin);
}
