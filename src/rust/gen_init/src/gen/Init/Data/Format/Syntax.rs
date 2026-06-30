// Lean compiler output
// Module: Init.Data.Format.Syntax
// Imports: Init.Data.ToString.Name Init.Data.ToString.Basic Init.Data.Format.Instances Init.Data.Format.Macro
use crate::ffi::{
    lean_array_get_size, lean_array_to_list, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
    lean_nat_to_int, lean_string_length, lean_string_utf8_extract,
};
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
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value:
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
    m_data: [58, 0],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Syntax_formatStxAux___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_formatStxAux___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_formatStxAux___closed__4_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__6_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__8_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__10_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__10_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__13_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__12_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Syntax_formatStxAux___closed__14_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__12_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Syntax_formatStxAux___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__14_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__13_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__15_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Syntax_formatStxAux___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_formatStxAux___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_formatStxAux___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_formatStxAux___closed__19_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__16_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__20_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__21_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__9_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__22_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Syntax_formatStxAux___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_formatStxAux___closed__23_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_formatStxAux___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_formatStxAux___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instToFormat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToFormat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToFormat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Syntax_instToFormat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instToString___closed__1_value: leanh::LeanClosureObject<5> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_comp as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_instToFormat___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_instToString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Syntax_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instToFormatTSyntax___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToFormatTSyntax___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToFormatTSyntax___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToFormatTSyntax___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instToStringTSyntax___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instToStringTSyntax___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instToStringTSyntax___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instToStringTSyntax___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
    mut v_showInfo_296_: u8,
    mut v_info_297_: *mut leanh::LeanObject,
    mut v_f_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_showInfo_296_ == 1 {
        match leanh::lean_obj_tag(v_info_297_) {
            0 => {
                let mut v_leading_299_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pos_300_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_trailing_301_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_302_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_303_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_304_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_stopPos_305_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_311_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_startPos_312_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_stopPos_313_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_leading_299_ = leanh::lean_ctor_get(v_info_297_, 0);
                leanh::lean_inc_ref(v_leading_299_);
                v_pos_300_ = leanh::lean_ctor_get(v_info_297_, 1);
                leanh::lean_inc(v_pos_300_);
                v_trailing_301_ = leanh::lean_ctor_get(v_info_297_, 2);
                leanh::lean_inc_ref(v_trailing_301_);
                v_endPos_302_ = leanh::lean_ctor_get(v_info_297_, 3);
                leanh::lean_inc(v_endPos_302_);
                leanh::lean_dec_ref_known(v_info_297_, 4);
                v_str_303_ = leanh::lean_ctor_get(v_leading_299_, 0);
                leanh::lean_inc_ref(v_str_303_);
                v_startPos_304_ = leanh::lean_ctor_get(v_leading_299_, 1);
                leanh::lean_inc(v_startPos_304_);
                v_stopPos_305_ = leanh::lean_ctor_get(v_leading_299_, 2);
                leanh::lean_inc(v_stopPos_305_);
                leanh::lean_dec_ref(v_leading_299_);
                v___x_306_ = lean_string_utf8_extract(v_str_303_, v_startPos_304_, v_stopPos_305_);
                leanh::lean_dec(v_stopPos_305_);
                leanh::lean_dec(v_startPos_304_);
                leanh::lean_dec_ref(v_str_303_);
                v___x_307_ = l_String_quote(v___x_306_);
                v___x_308_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_308_, 0, v___x_307_);
                v___x_309_ =
                    l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                v___x_310_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_310_, 0, v___x_308_);
                leanh::lean_ctor_set(v___x_310_, 1, v___x_309_);
                v_str_311_ = leanh::lean_ctor_get(v_trailing_301_, 0);
                leanh::lean_inc_ref(v_str_311_);
                v_startPos_312_ = leanh::lean_ctor_get(v_trailing_301_, 1);
                leanh::lean_inc(v_startPos_312_);
                v_stopPos_313_ = leanh::lean_ctor_get(v_trailing_301_, 2);
                leanh::lean_inc(v_stopPos_313_);
                leanh::lean_dec_ref(v_trailing_301_);
                v___x_314_ = l_Nat_reprFast(v_pos_300_);
                v___x_315_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
                v___x_316_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_316_, 0, v___x_310_);
                leanh::lean_ctor_set(v___x_316_, 1, v___x_315_);
                v___x_317_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_317_, 0, v___x_316_);
                leanh::lean_ctor_set(v___x_317_, 1, v___x_309_);
                v___x_318_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
                leanh::lean_ctor_set(v___x_318_, 1, v_f_298_);
                v___x_319_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_319_, 0, v___x_318_);
                leanh::lean_ctor_set(v___x_319_, 1, v___x_309_);
                v___x_320_ = l_Nat_reprFast(v_endPos_302_);
                v___x_321_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_321_, 0, v___x_320_);
                v___x_322_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_322_, 0, v___x_319_);
                leanh::lean_ctor_set(v___x_322_, 1, v___x_321_);
                v___x_323_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_323_, 0, v___x_322_);
                leanh::lean_ctor_set(v___x_323_, 1, v___x_309_);
                v___x_324_ = lean_string_utf8_extract(v_str_311_, v_startPos_312_, v_stopPos_313_);
                leanh::lean_dec(v_stopPos_313_);
                leanh::lean_dec(v_startPos_312_);
                leanh::lean_dec_ref(v_str_311_);
                v___x_325_ = l_String_quote(v___x_324_);
                v___x_326_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
                v___x_327_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_327_, 0, v___x_323_);
                leanh::lean_ctor_set(v___x_327_, 1, v___x_326_);
                return v___x_327_;
            }
            1 => {
                let mut v_canonical_328_: u8 = 0;
                v_canonical_328_ = leanh::lean_ctor_get_uint8(
                    v_info_297_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_canonical_328_ == 0 {
                    let mut v_pos_329_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_endPos_330_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_pos_329_ = leanh::lean_ctor_get(v_info_297_, 0);
                    leanh::lean_inc(v_pos_329_);
                    v_endPos_330_ = leanh::lean_ctor_get(v_info_297_, 1);
                    leanh::lean_inc(v_endPos_330_);
                    leanh::lean_dec_ref_known(v_info_297_, 2);
                    v___x_331_ = l_Nat_reprFast(v_pos_329_);
                    v___x_332_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_332_, 0, v___x_331_);
                    v___x_333_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                    v___x_334_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_334_, 0, v___x_332_);
                    leanh::lean_ctor_set(v___x_334_, 1, v___x_333_);
                    v___x_335_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_335_, 0, v___x_334_);
                    leanh::lean_ctor_set(v___x_335_, 1, v_f_298_);
                    v___x_336_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_336_, 0, v___x_335_);
                    leanh::lean_ctor_set(v___x_336_, 1, v___x_333_);
                    v___x_337_ = l_Nat_reprFast(v_endPos_330_);
                    v___x_338_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_338_, 0, v___x_337_);
                    v___x_339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_339_, 0, v___x_336_);
                    leanh::lean_ctor_set(v___x_339_, 1, v___x_338_);
                    return v___x_339_;
                } else {
                    let mut v_pos_340_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_endPos_341_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v_pos_340_ = leanh::lean_ctor_get(v_info_297_, 0);
                    leanh::lean_inc(v_pos_340_);
                    v_endPos_341_ = leanh::lean_ctor_get(v_info_297_, 1);
                    leanh::lean_inc(v_endPos_341_);
                    leanh::lean_dec_ref_known(v_info_297_, 2);
                    v___x_342_ = l_Nat_reprFast(v_pos_340_);
                    v___x_343_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_343_, 0, v___x_342_);
                    v___x_344_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3;
                    v___x_345_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_345_, 0, v___x_343_);
                    leanh::lean_ctor_set(v___x_345_, 1, v___x_344_);
                    v___x_346_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_346_, 0, v___x_345_);
                    leanh::lean_ctor_set(v___x_346_, 1, v_f_298_);
                    v___x_347_ =
                        l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1;
                    v___x_348_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_348_, 0, v___x_346_);
                    leanh::lean_ctor_set(v___x_348_, 1, v___x_347_);
                    v___x_349_ = l_Nat_reprFast(v_endPos_341_);
                    v___x_350_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_350_, 0, v___x_349_);
                    v___x_351_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_351_, 0, v___x_348_);
                    leanh::lean_ctor_set(v___x_351_, 1, v___x_350_);
                    return v___x_351_;
                }
            }
            _ => {
                leanh::lean_dec(v_info_297_);
                return v_f_298_;
            }
        }
    } else {
        leanh::lean_dec(v_info_297_);
        return v_f_298_;
    }
}
pub unsafe fn l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(
    mut v_showInfo_352_: *mut leanh::LeanObject,
    mut v_info_353_: *mut leanh::LeanObject,
    mut v_f_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_showInfo_boxed_355_: u8 = 0;
    let mut v_res_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_355_ = (leanh::lean_unbox(v_showInfo_352_) as u8);
    v_res_356_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
        v_showInfo_boxed_355_,
        v_info_353_,
        v_f_354_,
    );
    return v_res_356_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Syntax_formatStxAux_spec__0(
    mut v_a_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_nat_to_int(v_a_357_);
    return v___x_358_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(
    mut v_x_359_: *mut leanh::LeanObject,
    mut v_x_360_: *mut leanh::LeanObject,
    mut v_x_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_361_) == 0 {
                    leanh::lean_dec(v_x_359_);
                    return v_x_360_;
                } else {
                    v_head_362_ = leanh::lean_ctor_get(v_x_361_, 0);
                    v_tail_363_ = leanh::lean_ctor_get(v_x_361_, 1);
                    v_isSharedCheck_372_ = (!leanh::lean_is_exclusive(v_x_361_)) as u8;
                    if v_isSharedCheck_372_ == 0 {
                        v___x_365_ = v_x_361_;
                        v_isShared_366_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_363_);
                        leanh::lean_inc(v_head_362_);
                        leanh::lean_dec(v_x_361_);
                        v___x_365_ = leanh::lean_box(0);
                        v_isShared_366_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_359_);
                if v_isShared_366_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_365_, 5);
                    leanh::lean_ctor_set(v___x_365_, 1, v_x_359_);
                    leanh::lean_ctor_set(v___x_365_, 0, v_x_360_);
                    v___x_368_ = v___x_365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_371_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_371_, 0, v_x_360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_371_, 1, v_x_359_);
                    v___x_368_ = v_reuseFailAlloc_371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_369_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_369_, 0, v___x_368_);
                leanh::lean_ctor_set(v___x_369_, 1, v_head_362_);
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
    mut v_x_373_: *mut leanh::LeanObject,
    mut v_x_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_373_) == 0 {
        let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_374_);
        v___x_375_ = leanh::lean_box(0);
        return v___x_375_;
    } else {
        let mut v_tail_376_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_376_ = leanh::lean_ctor_get(v_x_373_, 1);
        if leanh::lean_obj_tag(v_tail_376_) == 0 {
            let mut v_head_377_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_374_);
            v_head_377_ = leanh::lean_ctor_get(v_x_373_, 0);
            leanh::lean_inc(v_head_377_);
            leanh::lean_dec_ref_known(v_x_373_, 2);
            return v_head_377_;
        } else {
            let mut v_head_378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_376_);
            v_head_378_ = leanh::lean_ctor_get(v_x_373_, 0);
            leanh::lean_inc(v_head_378_);
            leanh::lean_dec_ref_known(v_x_373_, 2);
            v___x_379_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(v_x_374_, v_head_378_, v_tail_376_);
            return v___x_379_;
        }
    }
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = l_Lean_Syntax_formatStxAux___closed__0;
    v___x_382_ = lean_string_length(v___x_381_);
    return v___x_382_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__2_once),
        _init_l_Lean_Syntax_formatStxAux___closed__2,
    );
    v___x_384_ = lean_nat_to_int(v___x_383_);
    return v___x_384_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ = l_Lean_Syntax_formatStxAux___closed__15;
    v___x_406_ = lean_string_length(v___x_405_);
    return v___x_406_;
}
pub unsafe fn _init_l_Lean_Syntax_formatStxAux___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__17_once),
        _init_l_Lean_Syntax_formatStxAux___closed__17,
    );
    v___x_408_ = lean_nat_to_int(v___x_407_);
    return v___x_408_;
}
pub unsafe fn l_Lean_Syntax_formatStxAux(
    mut v_maxDepth_420_: *mut leanh::LeanObject,
    mut v_showInfo_421_: u8,
    mut v_depth_422_: *mut leanh::LeanObject,
    mut v_x_423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depth_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_441_: u8 = 0;
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shorterName_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: u8 = 0;
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_header_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_474_: u8 = 0;
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: u8 = 0;
    let mut v_val_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v_val_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_423_) {
                0 => {
                    leanh::lean_dec(v_maxDepth_420_);
                    v___x_434_ = l_Lean_Syntax_formatStxAux___closed__7;
                    return v___x_434_;
                }
                1 => {
                    v_info_435_ = leanh::lean_ctor_get(v_x_423_, 0);
                    leanh::lean_inc(v_info_435_);
                    v_kind_436_ = leanh::lean_ctor_get(v_x_423_, 1);
                    leanh::lean_inc(v_kind_436_);
                    v_args_437_ = leanh::lean_ctor_get(v_x_423_, 2);
                    leanh::lean_inc_ref(v_args_437_);
                    leanh::lean_dec_ref_known(v_x_423_, 3);
                    v___x_438_ = leanh::lean_unsigned_to_nat(1);
                    v_depth_439_ = lean_nat_add(v_depth_422_, v___x_438_);
                    v___x_451_ = l_Lean_Syntax_formatStxAux___closed__11;
                    v___x_452_ = lean_name_eq(v_kind_436_, v___x_451_);
                    if v___x_452_ == 0 {
                        v___x_453_ = l_Lean_Syntax_formatStxAux___closed__14;
                        v___x_454_ = leanh::lean_box(0);
                        v_shorterName_455_ =
                            l_Lean_Name_replacePrefix(v_kind_436_, v___x_453_, v___x_454_);
                        v___x_456_ = 1;
                        v___x_457_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_shorterName_455_,
                                v___x_456_,
                            );
                        v___x_458_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_458_, 0, v___x_457_);
                        v_header_459_ =
                            l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                                v_showInfo_421_,
                                v_info_435_,
                                v___x_458_,
                            );
                        v___x_482_ = leanh::lean_unsigned_to_nat(0);
                        v___x_483_ = lean_array_get_size(v_args_437_);
                        v___x_484_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
                        if v___x_484_ == 0 {
                            v___y_474_ = v___x_484_;
                            state = 5;
                            continue;
                        } else {
                            if leanh::lean_obj_tag(v_maxDepth_420_) == 0 {
                                leanh::lean_inc(v_depth_439_);
                                v___y_480_ = v_depth_439_;
                                state = 6;
                                continue;
                            } else {
                                v_val_485_ = leanh::lean_ctor_get(v_maxDepth_420_, 0);
                                leanh::lean_inc(v_val_485_);
                                v___y_480_ = v_val_485_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_kind_436_);
                        leanh::lean_dec(v_info_435_);
                        v___x_486_ = leanh::lean_unsigned_to_nat(0);
                        v___x_487_ = lean_array_get_size(v_args_437_);
                        v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
                        if v___x_488_ == 0 {
                            v___y_441_ = v___x_488_;
                            state = 2;
                            continue;
                        } else {
                            if leanh::lean_obj_tag(v_maxDepth_420_) == 0 {
                                leanh::lean_inc(v_depth_439_);
                                v___y_449_ = v_depth_439_;
                                state = 3;
                                continue;
                            } else {
                                v_val_489_ = leanh::lean_ctor_get(v_maxDepth_420_, 0);
                                leanh::lean_inc(v_val_489_);
                                v___y_449_ = v_val_489_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
                2 => {
                    leanh::lean_dec(v_maxDepth_420_);
                    v_info_490_ = leanh::lean_ctor_get(v_x_423_, 0);
                    leanh::lean_inc(v_info_490_);
                    v_val_491_ = leanh::lean_ctor_get(v_x_423_, 1);
                    leanh::lean_inc_ref(v_val_491_);
                    leanh::lean_dec_ref_known(v_x_423_, 2);
                    v___x_492_ = l_String_quote(v_val_491_);
                    v___x_493_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_493_, 0, v___x_492_);
                    v___x_494_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                        v_showInfo_421_,
                        v_info_490_,
                        v___x_493_,
                    );
                    return v___x_494_;
                }
                _ => {
                    leanh::lean_dec(v_maxDepth_420_);
                    v_info_495_ = leanh::lean_ctor_get(v_x_423_, 0);
                    leanh::lean_inc(v_info_495_);
                    v_val_496_ = leanh::lean_ctor_get(v_x_423_, 2);
                    leanh::lean_inc(v_val_496_);
                    leanh::lean_dec_ref_known(v_x_423_, 4);
                    v___x_497_ = l_Lean_Syntax_formatStxAux___closed__23;
                    v___x_498_ = 1;
                    v___x_499_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_val_496_, v___x_498_,
                    );
                    v___x_500_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_500_, 0, v___x_499_);
                    v___x_501_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_501_, 0, v___x_497_);
                    leanh::lean_ctor_set(v___x_501_, 1, v___x_500_);
                    v___x_502_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(
                        v_showInfo_421_,
                        v_info_495_,
                        v___x_501_,
                    );
                    return v___x_502_;
                }
            },
            1 => {
                v___x_426_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__3_once),
                    _init_l_Lean_Syntax_formatStxAux___closed__3,
                );
                v___x_427_ = l_Lean_Syntax_formatStxAux___closed__4;
                v___x_428_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_428_, 0, v___x_427_);
                leanh::lean_ctor_set(v___x_428_, 1, v___y_425_);
                v___x_429_ = l_Lean_Syntax_formatStxAux___closed__5;
                v___x_430_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_430_, 0, v___x_428_);
                leanh::lean_ctor_set(v___x_430_, 1, v___x_429_);
                v___x_431_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_431_, 0, v___x_426_);
                leanh::lean_ctor_set(v___x_431_, 1, v___x_430_);
                v___x_432_ = 0;
                v___x_433_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_433_, 0, v___x_431_);
                leanh::lean_ctor_set_uint8(
                    v___x_433_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_432_,
                );
                return v___x_433_;
            }
            2 => {
                if v___y_441_ == 0 {
                    v___x_442_ = lean_array_to_list(v_args_437_);
                    v___x_443_ = leanh::lean_box(0);
                    v___x_444_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
                        v_maxDepth_420_,
                        v_showInfo_421_,
                        v_depth_439_,
                        v___x_442_,
                        v___x_443_,
                    );
                    leanh::lean_dec(v_depth_439_);
                    v___x_445_ = leanh::lean_box(1);
                    v___x_446_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
                        v___x_444_, v___x_445_,
                    );
                    v___y_425_ = v___x_446_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_depth_439_);
                    leanh::lean_dec_ref(v_args_437_);
                    leanh::lean_dec(v_maxDepth_420_);
                    v___x_447_ = l_Lean_Syntax_formatStxAux___closed__9;
                    v___y_425_ = v___x_447_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_450_ = lean_nat_dec_lt(v___y_449_, v_depth_439_);
                leanh::lean_dec(v___y_449_);
                v___y_441_ = v___x_450_;
                state = 2;
                continue;
            }
            4 => {
                v___x_462_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_462_, 0, v_header_459_);
                leanh::lean_ctor_set(v___x_462_, 1, v___y_461_);
                v___x_463_ = leanh::lean_box(1);
                v___x_464_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(
                    v___x_462_, v___x_463_,
                );
                v___x_465_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_formatStxAux___closed__18_once),
                    _init_l_Lean_Syntax_formatStxAux___closed__18,
                );
                v___x_466_ = l_Lean_Syntax_formatStxAux___closed__19;
                v___x_467_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_467_, 0, v___x_466_);
                leanh::lean_ctor_set(v___x_467_, 1, v___x_464_);
                v___x_468_ = l_Lean_Syntax_formatStxAux___closed__20;
                v___x_469_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_469_, 0, v___x_467_);
                leanh::lean_ctor_set(v___x_469_, 1, v___x_468_);
                v___x_470_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_470_, 0, v___x_465_);
                leanh::lean_ctor_set(v___x_470_, 1, v___x_469_);
                v___x_471_ = 0;
                v___x_472_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_472_, 0, v___x_470_);
                leanh::lean_ctor_set_uint8(
                    v___x_472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_471_,
                );
                return v___x_472_;
            }
            5 => {
                if v___y_474_ == 0 {
                    v___x_475_ = lean_array_to_list(v_args_437_);
                    v___x_476_ = leanh::lean_box(0);
                    v___x_477_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
                        v_maxDepth_420_,
                        v_showInfo_421_,
                        v_depth_439_,
                        v___x_475_,
                        v___x_476_,
                    );
                    leanh::lean_dec(v_depth_439_);
                    v___y_461_ = v___x_477_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_depth_439_);
                    leanh::lean_dec_ref(v_args_437_);
                    leanh::lean_dec(v_maxDepth_420_);
                    v___x_478_ = l_Lean_Syntax_formatStxAux___closed__21;
                    v___y_461_ = v___x_478_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_481_ = lean_nat_dec_lt(v___y_480_, v_depth_439_);
                leanh::lean_dec(v___y_480_);
                v___y_474_ = v___x_481_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
    mut v_maxDepth_503_: *mut leanh::LeanObject,
    mut v_showInfo_504_: u8,
    mut v_depth_505_: *mut leanh::LeanObject,
    mut v_a_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_506_) == 0 {
                    leanh::lean_dec(v_maxDepth_503_);
                    v___x_508_ = l_List_reverse___redArg(v_a_507_);
                    return v___x_508_;
                } else {
                    v_head_509_ = leanh::lean_ctor_get(v_a_506_, 0);
                    v_tail_510_ = leanh::lean_ctor_get(v_a_506_, 1);
                    v_isSharedCheck_519_ = (!leanh::lean_is_exclusive(v_a_506_)) as u8;
                    if v_isSharedCheck_519_ == 0 {
                        v___x_512_ = v_a_506_;
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_510_);
                        leanh::lean_inc(v_head_509_);
                        leanh::lean_dec(v_a_506_);
                        v___x_512_ = leanh::lean_box(0);
                        v_isShared_513_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_maxDepth_503_);
                v___x_514_ = l_Lean_Syntax_formatStxAux(
                    v_maxDepth_503_,
                    v_showInfo_504_,
                    v_depth_505_,
                    v_head_509_,
                );
                if v_isShared_513_ == 0 {
                    leanh::lean_ctor_set(v___x_512_, 1, v_a_507_);
                    leanh::lean_ctor_set(v___x_512_, 0, v___x_514_);
                    v___x_516_ = v___x_512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_507_);
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
    mut v_maxDepth_520_: *mut leanh::LeanObject,
    mut v_showInfo_521_: *mut leanh::LeanObject,
    mut v_depth_522_: *mut leanh::LeanObject,
    mut v_a_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_showInfo_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_525_ = (leanh::lean_unbox(v_showInfo_521_) as u8);
    v_res_526_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(
        v_maxDepth_520_,
        v_showInfo_boxed_525_,
        v_depth_522_,
        v_a_523_,
        v_a_524_,
    );
    leanh::lean_dec(v_depth_522_);
    return v_res_526_;
}
pub unsafe fn l_Lean_Syntax_formatStxAux___boxed(
    mut v_maxDepth_527_: *mut leanh::LeanObject,
    mut v_showInfo_528_: *mut leanh::LeanObject,
    mut v_depth_529_: *mut leanh::LeanObject,
    mut v_x_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_showInfo_boxed_531_: u8 = 0;
    let mut v_res_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_531_ = (leanh::lean_unbox(v_showInfo_528_) as u8);
    v_res_532_ = l_Lean_Syntax_formatStxAux(
        v_maxDepth_527_,
        v_showInfo_boxed_531_,
        v_depth_529_,
        v_x_530_,
    );
    leanh::lean_dec(v_depth_529_);
    return v_res_532_;
}
pub unsafe fn l_Lean_Syntax_formatStx(
    mut v_stx_533_: *mut leanh::LeanObject,
    mut v_maxDepth_534_: *mut leanh::LeanObject,
    mut v_showInfo_535_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ = leanh::lean_unsigned_to_nat(0);
    v___x_537_ =
        l_Lean_Syntax_formatStxAux(v_maxDepth_534_, v_showInfo_535_, v___x_536_, v_stx_533_);
    return v___x_537_;
}
pub unsafe fn l_Lean_Syntax_formatStx___boxed(
    mut v_stx_538_: *mut leanh::LeanObject,
    mut v_maxDepth_539_: *mut leanh::LeanObject,
    mut v_showInfo_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_showInfo_boxed_541_: u8 = 0;
    let mut v_res_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_showInfo_boxed_541_ = (leanh::lean_unbox(v_showInfo_540_) as u8);
    v_res_542_ = l_Lean_Syntax_formatStx(v_stx_538_, v_maxDepth_539_, v_showInfo_boxed_541_);
    return v_res_542_;
}
pub unsafe fn l_Lean_Syntax_instToFormat___lam__0(
    mut v_stx_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = leanh::lean_box(0);
    v___x_545_ = 0;
    v___x_546_ = l_Lean_Syntax_formatStx(v_stx_543_, v___x_544_, v___x_545_);
    return v___x_546_;
}
pub unsafe fn l_Lean_Syntax_instToString___lam__0(
    mut v_f_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Std_Format_defWidth;
    v___x_551_ = leanh::lean_unsigned_to_nat(0);
    v___x_552_ = l_Std_Format_pretty(v_f_549_, v___x_550_, v___x_551_, v___x_551_);
    return v___x_552_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax___lam__0(
    mut v_x_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_559_ = leanh::lean_box(0);
    v___x_560_ = 0;
    v___x_561_ = l_Lean_Syntax_formatStx(v_x_558_, v___x_559_, v___x_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax(
    mut v_k_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_564_ = l_Lean_Syntax_instToFormatTSyntax___closed__0;
    return v___f_564_;
}
pub unsafe fn l_Lean_Syntax_instToFormatTSyntax___boxed(
    mut v_k_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Lean_Syntax_instToFormatTSyntax(v_k_565_);
    leanh::lean_dec(v_k_565_);
    return v_res_566_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax___lam__0(
    mut v_x_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = leanh::lean_box(0);
    v___x_569_ = 0;
    v___x_570_ = l_Lean_Syntax_formatStx(v_x_567_, v___x_568_, v___x_569_);
    v___x_571_ = l_Std_Format_defWidth;
    v___x_572_ = leanh::lean_unsigned_to_nat(0);
    v___x_573_ = l_Std_Format_pretty(v___x_570_, v___x_571_, v___x_572_, v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax(
    mut v_k_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_576_ = l_Lean_Syntax_instToStringTSyntax___closed__0;
    return v___f_576_;
}
pub unsafe fn l_Lean_Syntax_instToStringTSyntax___boxed(
    mut v_k_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Syntax_instToStringTSyntax(v_k_577_);
    leanh::lean_dec(v_k_577_);
    return v_res_578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Format_Syntax(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Format_Syntax(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Format_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Format_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Format_Syntax(builtin);
}