// Lean compiler output
// Module: Lake.Config.Dynlib
// Imports: Lake.Config.OutFormat
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::System::FilePath::l_System_FilePath_parent;
use crate::r#gen::Lake::Config::OutFormat::{
    initialize_Lake_Config_OutFormat, runtime_initialize_Lake_Config_OutFormat,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_array_get_size, lean_array_to_list, lean_nat_dec_eq,
};
pub static l_Lake_instInhabitedDynlib_default___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Lake_instInhabitedDynlib_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedDynlib_default___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_instInhabitedDynlib_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedDynlib_default___closed__2_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__1_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instInhabitedDynlib_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDynlib_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDynlib: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__4_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__1_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 97, 116, 104, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDynlib_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDynlib_repr___redArg___closed__8_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value:
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
    m_data: [44, 0],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value:
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
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__10_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__11_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__12_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [112, 108, 117, 103, 105, 110, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__13_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDynlib_repr___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDynlib_repr___redArg___closed__15_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 101, 112, 115, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__16_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7_value:
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
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value:
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
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8_value:
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
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value:
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
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10_value:
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
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDynlib_repr___redArg___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprDynlib_repr___redArg___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDynlib_repr___redArg___closed__20_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__17_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__21_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDynlib___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprDynlib_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprDynlib___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprDynlib: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Dynlib_instToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Dynlib_instToJson___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Dynlib_instToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Dynlib_instToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Dynlib_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Dynlib_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Dynlib_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Dynlib_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Dynlib_instCoeFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Lake_instReprDynlib_repr_spec__1(
    mut v_a_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = lean_nat_to_int(v_a_213_);
    return v___x_214_;
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_227_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_228_ = lean_nat_to_int(v___x_227_);
    return v___x_228_;
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_242_ = lean_nat_to_int(v___x_241_);
    return v___x_242_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(
    mut v_x_249_: *mut crate::leanh::LeanObject,
    mut v_x_250_: *mut crate::leanh::LeanObject,
    mut v_x_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_256_: u8 = 0;
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_251_) == 0 {
                    crate::leanh::lean_dec(v_x_249_);
                    return v_x_250_;
                } else {
                    v_head_252_ = crate::leanh::lean_ctor_get(v_x_251_, 0);
                    v_tail_253_ = crate::leanh::lean_ctor_get(v_x_251_, 1);
                    v_isSharedCheck_263_ = (!crate::leanh::lean_is_exclusive(v_x_251_)) as u8;
                    if v_isSharedCheck_263_ == 0 {
                        v___x_255_ = v_x_251_;
                        v_isShared_256_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_253_);
                        crate::leanh::lean_inc(v_head_252_);
                        crate::leanh::lean_dec(v_x_251_);
                        v___x_255_ = crate::leanh::lean_box(0);
                        v_isShared_256_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_249_);
                if v_isShared_256_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_255_, 5);
                    crate::leanh::lean_ctor_set(v___x_255_, 1, v_x_249_);
                    crate::leanh::lean_ctor_set(v___x_255_, 0, v_x_250_);
                    v___x_258_ = v___x_255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_262_, 0, v_x_250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_262_, 1, v_x_249_);
                    v___x_258_ = v_reuseFailAlloc_262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_259_ = l_Lake_instReprDynlib_repr___redArg(v_head_252_);
                v___x_260_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_260_, 0, v___x_258_);
                crate::leanh::lean_ctor_set(v___x_260_, 1, v___x_259_);
                v___x_261_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(v_x_249_, v___x_260_, v_tail_253_);
                return v___x_261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(
    mut v_x_264_: *mut crate::leanh::LeanObject,
    mut v_x_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_264_) == 0 {
        let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_265_);
        v___x_266_ = crate::leanh::lean_box(0);
        return v___x_266_;
    } else {
        let mut v_tail_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_267_ = crate::leanh::lean_ctor_get(v_x_264_, 1);
        if crate::leanh::lean_obj_tag(v_tail_267_) == 0 {
            let mut v_head_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_265_);
            v_head_268_ = crate::leanh::lean_ctor_get(v_x_264_, 0);
            crate::leanh::lean_inc(v_head_268_);
            crate::leanh::lean_dec_ref_known(v_x_264_, 2);
            v___x_269_ = l_Lake_instReprDynlib_repr___redArg(v_head_268_);
            return v___x_269_;
        } else {
            let mut v_head_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_267_);
            v_head_270_ = crate::leanh::lean_ctor_get(v_x_264_, 0);
            crate::leanh::lean_inc(v_head_270_);
            crate::leanh::lean_dec_ref_known(v_x_264_, 2);
            v___x_271_ = l_Lake_instReprDynlib_repr___redArg(v_head_270_);
            v___x_272_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(v_x_265_, v___x_271_, v_tail_267_);
            return v___x_272_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0;
    v___x_275_ = lean_string_length(v___x_274_);
    return v___x_275_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_276_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5,
    );
    v___x_277_ = lean_nat_to_int(v___x_276_);
    return v___x_277_;
}
pub unsafe fn l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(
    mut v_xs_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: u8 = 0;
    v___x_287_ = lean_array_get_size(v_xs_286_);
    v___x_288_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
    if v___x_289_ == 0 {
        let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_290_ = lean_array_to_list(v_xs_286_);
        v___x_291_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3;
        v___x_292_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(v___x_290_, v___x_291_);
        v___x_293_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6,
        );
        v___x_294_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7;
        v___x_295_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_295_, 0, v___x_294_);
        crate::leanh::lean_ctor_set(v___x_295_, 1, v___x_292_);
        v___x_296_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8;
        v___x_297_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_297_, 0, v___x_295_);
        crate::leanh::lean_ctor_set(v___x_297_, 1, v___x_296_);
        v___x_298_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_298_, 0, v___x_293_);
        crate::leanh::lean_ctor_set(v___x_298_, 1, v___x_297_);
        v___x_299_ = l_Std_Format_fill(v___x_298_);
        return v___x_299_;
    } else {
        let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_286_);
        v___x_300_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10;
        return v___x_300_;
    }
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_302_ = l_Lake_instReprDynlib_repr___redArg___closed__0;
    v___x_303_ = lean_string_length(v___x_302_);
    return v___x_303_;
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__18_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__18,
    );
    v___x_305_ = lean_nat_to_int(v___x_304_);
    return v___x_305_;
}
pub unsafe fn l_Lake_instReprDynlib_repr___redArg(
    mut v_x_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugin_314_: u8 = 0;
    let mut v_deps_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_326_: u8 = 0;
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_path_312_ = crate::leanh::lean_ctor_get(v_x_311_, 0);
    crate::leanh::lean_inc_ref(v_path_312_);
    v_name_313_ = crate::leanh::lean_ctor_get(v_x_311_, 1);
    crate::leanh::lean_inc_ref(v_name_313_);
    v_plugin_314_ = crate::leanh::lean_ctor_get_uint8(
        v_x_311_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v_deps_315_ = crate::leanh::lean_ctor_get(v_x_311_, 2);
    crate::leanh::lean_inc_ref(v_deps_315_);
    crate::leanh::lean_dec_ref(v_x_311_);
    v___x_316_ = l_Lake_instReprDynlib_repr___redArg___closed__5;
    v___x_317_ = l_Lake_instReprDynlib_repr___redArg___closed__6;
    v___x_318_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__7_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__7,
    );
    v___x_319_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_320_ = l_Lake_instReprDynlib_repr___redArg___closed__9;
    v___x_321_ = l_String_quote(v_path_312_);
    v___x_322_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_321_);
    v___x_323_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_323_, 0, v___x_320_);
    crate::leanh::lean_ctor_set(v___x_323_, 1, v___x_322_);
    v___x_324_ = l_Repr_addAppParen(v___x_323_, v___x_319_);
    v___x_325_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_325_, 0, v___x_318_);
    crate::leanh::lean_ctor_set(v___x_325_, 1, v___x_324_);
    v___x_326_ = 0;
    v___x_327_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_327_, 0, v___x_325_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_327_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_328_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_328_, 0, v___x_317_);
    crate::leanh::lean_ctor_set(v___x_328_, 1, v___x_327_);
    v___x_329_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2;
    v___x_330_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_330_, 0, v___x_328_);
    crate::leanh::lean_ctor_set(v___x_330_, 1, v___x_329_);
    v___x_331_ = crate::leanh::lean_box(1);
    v___x_332_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_332_, 0, v___x_330_);
    crate::leanh::lean_ctor_set(v___x_332_, 1, v___x_331_);
    v___x_333_ = l_Lake_instReprDynlib_repr___redArg___closed__11;
    v___x_334_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_334_, 0, v___x_332_);
    crate::leanh::lean_ctor_set(v___x_334_, 1, v___x_333_);
    v___x_335_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_335_, 0, v___x_334_);
    crate::leanh::lean_ctor_set(v___x_335_, 1, v___x_316_);
    v___x_336_ = l_String_quote(v_name_313_);
    v___x_337_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_337_, 0, v___x_336_);
    v___x_338_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_338_, 0, v___x_318_);
    crate::leanh::lean_ctor_set(v___x_338_, 1, v___x_337_);
    v___x_339_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_339_, 0, v___x_338_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_339_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_340_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_335_);
    crate::leanh::lean_ctor_set(v___x_340_, 1, v___x_339_);
    v___x_341_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_341_, 0, v___x_340_);
    crate::leanh::lean_ctor_set(v___x_341_, 1, v___x_329_);
    v___x_342_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_342_, 0, v___x_341_);
    crate::leanh::lean_ctor_set(v___x_342_, 1, v___x_331_);
    v___x_343_ = l_Lake_instReprDynlib_repr___redArg___closed__13;
    v___x_344_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_344_, 0, v___x_342_);
    crate::leanh::lean_ctor_set(v___x_344_, 1, v___x_343_);
    v___x_345_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
    crate::leanh::lean_ctor_set(v___x_345_, 1, v___x_316_);
    v___x_346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__14_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__14,
    );
    v___x_347_ = l_Bool_repr___redArg(v_plugin_314_);
    v___x_348_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_348_, 0, v___x_346_);
    crate::leanh::lean_ctor_set(v___x_348_, 1, v___x_347_);
    v___x_349_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_349_, 0, v___x_348_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_349_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_350_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_350_, 0, v___x_345_);
    crate::leanh::lean_ctor_set(v___x_350_, 1, v___x_349_);
    v___x_351_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_351_, 0, v___x_350_);
    crate::leanh::lean_ctor_set(v___x_351_, 1, v___x_329_);
    v___x_352_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_352_, 0, v___x_351_);
    crate::leanh::lean_ctor_set(v___x_352_, 1, v___x_331_);
    v___x_353_ = l_Lake_instReprDynlib_repr___redArg___closed__16;
    v___x_354_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_354_, 0, v___x_352_);
    crate::leanh::lean_ctor_set(v___x_354_, 1, v___x_353_);
    v___x_355_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_355_, 0, v___x_354_);
    crate::leanh::lean_ctor_set(v___x_355_, 1, v___x_316_);
    v___x_356_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(v_deps_315_);
    v___x_357_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_357_, 0, v___x_318_);
    crate::leanh::lean_ctor_set(v___x_357_, 1, v___x_356_);
    v___x_358_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_358_, 0, v___x_357_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_358_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_359_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_359_, 0, v___x_355_);
    crate::leanh::lean_ctor_set(v___x_359_, 1, v___x_358_);
    v___x_360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__19_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__19,
    );
    v___x_361_ = l_Lake_instReprDynlib_repr___redArg___closed__20;
    v___x_362_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_362_, 0, v___x_361_);
    crate::leanh::lean_ctor_set(v___x_362_, 1, v___x_359_);
    v___x_363_ = l_Lake_instReprDynlib_repr___redArg___closed__21;
    v___x_364_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_364_, 0, v___x_362_);
    crate::leanh::lean_ctor_set(v___x_364_, 1, v___x_363_);
    v___x_365_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_365_, 0, v___x_360_);
    crate::leanh::lean_ctor_set(v___x_365_, 1, v___x_364_);
    v___x_366_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_366_, 0, v___x_365_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_366_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_326_,
    );
    return v___x_366_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_367_: *mut crate::leanh::LeanObject,
    mut v_x_368_: *mut crate::leanh::LeanObject,
    mut v_x_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_374_: u8 = 0;
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_369_) == 0 {
                    crate::leanh::lean_dec(v_x_367_);
                    return v_x_368_;
                } else {
                    v_head_370_ = crate::leanh::lean_ctor_get(v_x_369_, 0);
                    v_tail_371_ = crate::leanh::lean_ctor_get(v_x_369_, 1);
                    v_isSharedCheck_381_ = (!crate::leanh::lean_is_exclusive(v_x_369_)) as u8;
                    if v_isSharedCheck_381_ == 0 {
                        v___x_373_ = v_x_369_;
                        v_isShared_374_ = v_isSharedCheck_381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_371_);
                        crate::leanh::lean_inc(v_head_370_);
                        crate::leanh::lean_dec(v_x_369_);
                        v___x_373_ = crate::leanh::lean_box(0);
                        v_isShared_374_ = v_isSharedCheck_381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_367_);
                if v_isShared_374_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_373_, 5);
                    crate::leanh::lean_ctor_set(v___x_373_, 1, v_x_367_);
                    crate::leanh::lean_ctor_set(v___x_373_, 0, v_x_368_);
                    v___x_376_ = v___x_373_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_380_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_380_, 0, v_x_368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_380_, 1, v_x_367_);
                    v___x_376_ = v_reuseFailAlloc_380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_377_ = l_Lake_instReprDynlib_repr___redArg(v_head_370_);
                v___x_378_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_378_, 0, v___x_376_);
                crate::leanh::lean_ctor_set(v___x_378_, 1, v___x_377_);
                v_x_368_ = v___x_378_;
                v_x_369_ = v_tail_371_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprDynlib_repr(
    mut v_x_382_: *mut crate::leanh::LeanObject,
    mut v_prec_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = l_Lake_instReprDynlib_repr___redArg(v_x_382_);
    return v___x_384_;
}
pub unsafe fn l_Lake_instReprDynlib_repr___boxed(
    mut v_x_385_: *mut crate::leanh::LeanObject,
    mut v_prec_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_387_ = l_Lake_instReprDynlib_repr(v_x_385_, v_prec_386_);
    crate::leanh::lean_dec(v_prec_386_);
    return v_res_387_;
}
pub unsafe fn l_Lake_Dynlib_dir_x3f(
    mut v_self_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_path_391_ = crate::leanh::lean_ctor_get(v_self_390_, 0);
    crate::leanh::lean_inc_ref(v_path_391_);
    crate::leanh::lean_dec_ref(v_self_390_);
    v___x_392_ = l_System_FilePath_parent(v_path_391_);
    return v___x_392_;
}
pub unsafe fn l_Lake_Dynlib_instToJson___lam__0(
    mut v_x_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_path_394_ = crate::leanh::lean_ctor_get(v_x_393_, 0);
    crate::leanh::lean_inc_ref(v_path_394_);
    v___x_395_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_395_, 0, v_path_394_);
    return v___x_395_;
}
pub unsafe fn l_Lake_Dynlib_instToJson___lam__0___boxed(
    mut v_x_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_397_ = l_Lake_Dynlib_instToJson___lam__0(v_x_396_);
    crate::leanh::lean_dec_ref(v_x_396_);
    return v_res_397_;
}
pub unsafe fn l_Lake_Dynlib_instToString___lam__0(
    mut v_x_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_path_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_path_401_ = crate::leanh::lean_ctor_get(v_x_400_, 0);
    crate::leanh::lean_inc_ref(v_path_401_);
    return v_path_401_;
}
pub unsafe fn l_Lake_Dynlib_instToString___lam__0___boxed(
    mut v_x_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_403_ = l_Lake_Dynlib_instToString___lam__0(v_x_402_);
    crate::leanh::lean_dec_ref(v_x_402_);
    return v_res_403_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Dynlib(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_OutFormat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Dynlib(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Dynlib(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_OutFormat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Dynlib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Dynlib(builtin);
}
