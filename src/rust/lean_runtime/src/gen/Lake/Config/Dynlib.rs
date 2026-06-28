// Lean compiler output
// Module: Lake.Config.Dynlib
// Imports: Lake.Config.OutFormat
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::System::FilePath::l_System_FilePath_parent;
use crate::r#gen::Lake::Config::OutFormat::{
    initialize_Lake_Config_OutFormat, runtime_initialize_Lake_Config_OutFormat,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_instInhabitedDynlib_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedDynlib_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedDynlib_default___closed__1_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_instInhabitedDynlib_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__1_value) as *mut LeanObject;
pub static l_Lake_instInhabitedDynlib_default___closed__2_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__1_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedDynlib_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedDynlib_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedDynlib: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDynlib_default___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lake_instReprDynlib_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprDynlib_repr___redArg___closed__8_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__10_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__10_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__11_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__12_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__12_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__13_value) as *mut LeanObject;
static mut l_Lake_instReprDynlib_repr___redArg___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDynlib_repr___redArg___closed__15_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__15_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__16_value) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value)
        as *mut LeanObject;
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lake_instReprDynlib_repr___redArg___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprDynlib_repr___redArg___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprDynlib_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDynlib_repr___redArg___closed__20_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__20_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__17_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprDynlib_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__17_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib_repr___redArg___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprDynlib_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib_repr___redArg___closed__21_value) as *mut LeanObject;
pub static l_Lake_instReprDynlib___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprDynlib_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprDynlib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprDynlib: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDynlib___closed__0_value) as *mut LeanObject;
pub static l_Lake_Dynlib_instToJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Dynlib_instToJson___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Dynlib_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Dynlib_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_Dynlib_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Dynlib_instToString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Dynlib_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Dynlib_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Dynlib_instCoeFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Dynlib_instToString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Lake_instReprDynlib_repr_spec__1(
    mut v_a_213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    v___x_214_ = lean_nat_to_int(v_a_213_);
    return v___x_214_;
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_227_ = lean_unsigned_to_nat(8);
    v___x_228_ = lean_nat_to_int(v___x_227_);
    return v___x_228_;
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    v___x_241_ = lean_unsigned_to_nat(10);
    v___x_242_ = lean_nat_to_int(v___x_241_);
    return v___x_242_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(
    mut v_x_249_: *mut LeanObject,
    mut v_x_250_: *mut LeanObject,
    mut v_x_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_256_: u8 = 0;
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_251_) == 0 {
                    lean_dec(v_x_249_);
                    return v_x_250_;
                } else {
                    v_head_252_ = lean_ctor_get(v_x_251_, 0);
                    v_tail_253_ = lean_ctor_get(v_x_251_, 1);
                    v_isSharedCheck_263_ = (!lean_is_exclusive(v_x_251_)) as u8;
                    if v_isSharedCheck_263_ == 0 {
                        v___x_255_ = v_x_251_;
                        v_isShared_256_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_253_);
                        lean_inc(v_head_252_);
                        lean_dec(v_x_251_);
                        v___x_255_ = lean_box(0);
                        v_isShared_256_ = v_isSharedCheck_263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_249_);
                if v_isShared_256_ == 0 {
                    lean_ctor_set_tag(v___x_255_, 5);
                    lean_ctor_set(v___x_255_, 1, v_x_249_);
                    lean_ctor_set(v___x_255_, 0, v_x_250_);
                    v___x_258_ = v___x_255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_262_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_262_, 0, v_x_250_);
                    lean_ctor_set(v_reuseFailAlloc_262_, 1, v_x_249_);
                    v___x_258_ = v_reuseFailAlloc_262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_259_ = l_Lake_instReprDynlib_repr___redArg(v_head_252_);
                v___x_260_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_260_, 0, v___x_258_);
                lean_ctor_set(v___x_260_, 1, v___x_259_);
                v___x_261_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(v_x_249_, v___x_260_, v_tail_253_);
                return v___x_261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(
    mut v_x_264_: *mut LeanObject,
    mut v_x_265_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_264_) == 0 {
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_265_);
        v___x_266_ = lean_box(0);
        return v___x_266_;
    } else {
        let mut v_tail_267_: *mut LeanObject = core::ptr::null_mut();
        v_tail_267_ = lean_ctor_get(v_x_264_, 1);
        if lean_obj_tag(v_tail_267_) == 0 {
            let mut v_head_268_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_265_);
            v_head_268_ = lean_ctor_get(v_x_264_, 0);
            lean_inc(v_head_268_);
            lean_dec_ref_known(v_x_264_, 2);
            v___x_269_ = l_Lake_instReprDynlib_repr___redArg(v_head_268_);
            return v___x_269_;
        } else {
            let mut v_head_270_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_267_);
            v_head_270_ = lean_ctor_get(v_x_264_, 0);
            lean_inc(v_head_270_);
            lean_dec_ref_known(v_x_264_, 2);
            v___x_271_ = l_Lake_instReprDynlib_repr___redArg(v_head_270_);
            v___x_272_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2(v_x_265_, v___x_271_, v_tail_267_);
            return v___x_272_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    v___x_274_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__0;
    v___x_275_ = lean_string_length(v___x_274_);
    return v___x_275_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    v___x_276_ = lean_obj_once(
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
    mut v_xs_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: u8 = 0;
    v___x_287_ = lean_array_get_size(v_xs_286_);
    v___x_288_ = lean_unsigned_to_nat(0);
    v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
    if v___x_289_ == 0 {
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
        v___x_290_ = lean_array_to_list(v_xs_286_);
        v___x_291_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__3;
        v___x_292_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0(v___x_290_, v___x_291_);
        v___x_293_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__6,
        );
        v___x_294_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__7;
        v___x_295_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_295_, 0, v___x_294_);
        lean_ctor_set(v___x_295_, 1, v___x_292_);
        v___x_296_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__8;
        v___x_297_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_297_, 0, v___x_295_);
        lean_ctor_set(v___x_297_, 1, v___x_296_);
        v___x_298_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_298_, 0, v___x_293_);
        lean_ctor_set(v___x_298_, 1, v___x_297_);
        v___x_299_ = l_Std_Format_fill(v___x_298_);
        return v___x_299_;
    } else {
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_286_);
        v___x_300_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__10;
        return v___x_300_;
    }
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__18() -> *mut LeanObject {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v___x_302_ = l_Lake_instReprDynlib_repr___redArg___closed__0;
    v___x_303_ = lean_string_length(v___x_302_);
    return v___x_303_;
}
pub unsafe fn _init_l_Lake_instReprDynlib_repr___redArg___closed__19() -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    v___x_304_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__18_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__18,
    );
    v___x_305_ = lean_nat_to_int(v___x_304_);
    return v___x_305_;
}
pub unsafe fn l_Lake_instReprDynlib_repr___redArg(
    mut v_x_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugin_314_: u8 = 0;
    let mut v_deps_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: u8 = 0;
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    v_path_312_ = lean_ctor_get(v_x_311_, 0);
    lean_inc_ref(v_path_312_);
    v_name_313_ = lean_ctor_get(v_x_311_, 1);
    lean_inc_ref(v_name_313_);
    v_plugin_314_ = lean_ctor_get_uint8(
        v_x_311_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_deps_315_ = lean_ctor_get(v_x_311_, 2);
    lean_inc_ref(v_deps_315_);
    lean_dec_ref(v_x_311_);
    v___x_316_ = l_Lake_instReprDynlib_repr___redArg___closed__5;
    v___x_317_ = l_Lake_instReprDynlib_repr___redArg___closed__6;
    v___x_318_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__7_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__7,
    );
    v___x_319_ = lean_unsigned_to_nat(0);
    v___x_320_ = l_Lake_instReprDynlib_repr___redArg___closed__9;
    v___x_321_ = l_String_quote(v_path_312_);
    v___x_322_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_322_, 0, v___x_321_);
    v___x_323_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_323_, 0, v___x_320_);
    lean_ctor_set(v___x_323_, 1, v___x_322_);
    v___x_324_ = l_Repr_addAppParen(v___x_323_, v___x_319_);
    v___x_325_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_325_, 0, v___x_318_);
    lean_ctor_set(v___x_325_, 1, v___x_324_);
    v___x_326_ = 0;
    v___x_327_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_327_, 0, v___x_325_);
    lean_ctor_set_uint8(
        v___x_327_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_328_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_328_, 0, v___x_317_);
    lean_ctor_set(v___x_328_, 1, v___x_327_);
    v___x_329_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0___closed__2;
    v___x_330_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_330_, 0, v___x_328_);
    lean_ctor_set(v___x_330_, 1, v___x_329_);
    v___x_331_ = lean_box(1);
    v___x_332_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_332_, 0, v___x_330_);
    lean_ctor_set(v___x_332_, 1, v___x_331_);
    v___x_333_ = l_Lake_instReprDynlib_repr___redArg___closed__11;
    v___x_334_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_334_, 0, v___x_332_);
    lean_ctor_set(v___x_334_, 1, v___x_333_);
    v___x_335_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_335_, 0, v___x_334_);
    lean_ctor_set(v___x_335_, 1, v___x_316_);
    v___x_336_ = l_String_quote(v_name_313_);
    v___x_337_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_337_, 0, v___x_336_);
    v___x_338_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_338_, 0, v___x_318_);
    lean_ctor_set(v___x_338_, 1, v___x_337_);
    v___x_339_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_339_, 0, v___x_338_);
    lean_ctor_set_uint8(
        v___x_339_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_340_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_340_, 0, v___x_335_);
    lean_ctor_set(v___x_340_, 1, v___x_339_);
    v___x_341_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_341_, 0, v___x_340_);
    lean_ctor_set(v___x_341_, 1, v___x_329_);
    v___x_342_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_342_, 0, v___x_341_);
    lean_ctor_set(v___x_342_, 1, v___x_331_);
    v___x_343_ = l_Lake_instReprDynlib_repr___redArg___closed__13;
    v___x_344_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_344_, 0, v___x_342_);
    lean_ctor_set(v___x_344_, 1, v___x_343_);
    v___x_345_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_345_, 0, v___x_344_);
    lean_ctor_set(v___x_345_, 1, v___x_316_);
    v___x_346_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__14_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__14,
    );
    v___x_347_ = l_Bool_repr___redArg(v_plugin_314_);
    v___x_348_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_348_, 0, v___x_346_);
    lean_ctor_set(v___x_348_, 1, v___x_347_);
    v___x_349_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_349_, 0, v___x_348_);
    lean_ctor_set_uint8(
        v___x_349_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_350_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_350_, 0, v___x_345_);
    lean_ctor_set(v___x_350_, 1, v___x_349_);
    v___x_351_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_351_, 0, v___x_350_);
    lean_ctor_set(v___x_351_, 1, v___x_329_);
    v___x_352_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_352_, 0, v___x_351_);
    lean_ctor_set(v___x_352_, 1, v___x_331_);
    v___x_353_ = l_Lake_instReprDynlib_repr___redArg___closed__16;
    v___x_354_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_354_, 0, v___x_352_);
    lean_ctor_set(v___x_354_, 1, v___x_353_);
    v___x_355_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_355_, 0, v___x_354_);
    lean_ctor_set(v___x_355_, 1, v___x_316_);
    v___x_356_ = l_Array_repr___at___00Lake_instReprDynlib_repr_spec__0(v_deps_315_);
    v___x_357_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_357_, 0, v___x_318_);
    lean_ctor_set(v___x_357_, 1, v___x_356_);
    v___x_358_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_358_, 0, v___x_357_);
    lean_ctor_set_uint8(
        v___x_358_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_326_,
    );
    v___x_359_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_359_, 0, v___x_355_);
    lean_ctor_set(v___x_359_, 1, v___x_358_);
    v___x_360_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instReprDynlib_repr___redArg___closed__19_once),
        _init_l_Lake_instReprDynlib_repr___redArg___closed__19,
    );
    v___x_361_ = l_Lake_instReprDynlib_repr___redArg___closed__20;
    v___x_362_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_362_, 0, v___x_361_);
    lean_ctor_set(v___x_362_, 1, v___x_359_);
    v___x_363_ = l_Lake_instReprDynlib_repr___redArg___closed__21;
    v___x_364_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_364_, 0, v___x_362_);
    lean_ctor_set(v___x_364_, 1, v___x_363_);
    v___x_365_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_365_, 0, v___x_360_);
    lean_ctor_set(v___x_365_, 1, v___x_364_);
    v___x_366_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_366_, 0, v___x_365_);
    lean_ctor_set_uint8(
        v___x_366_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_326_,
    );
    return v___x_366_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprDynlib_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_367_: *mut LeanObject,
    mut v_x_368_: *mut LeanObject,
    mut v_x_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_374_: u8 = 0;
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_369_) == 0 {
                    lean_dec(v_x_367_);
                    return v_x_368_;
                } else {
                    v_head_370_ = lean_ctor_get(v_x_369_, 0);
                    v_tail_371_ = lean_ctor_get(v_x_369_, 1);
                    v_isSharedCheck_381_ = (!lean_is_exclusive(v_x_369_)) as u8;
                    if v_isSharedCheck_381_ == 0 {
                        v___x_373_ = v_x_369_;
                        v_isShared_374_ = v_isSharedCheck_381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_371_);
                        lean_inc(v_head_370_);
                        lean_dec(v_x_369_);
                        v___x_373_ = lean_box(0);
                        v_isShared_374_ = v_isSharedCheck_381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_367_);
                if v_isShared_374_ == 0 {
                    lean_ctor_set_tag(v___x_373_, 5);
                    lean_ctor_set(v___x_373_, 1, v_x_367_);
                    lean_ctor_set(v___x_373_, 0, v_x_368_);
                    v___x_376_ = v___x_373_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_380_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_380_, 0, v_x_368_);
                    lean_ctor_set(v_reuseFailAlloc_380_, 1, v_x_367_);
                    v___x_376_ = v_reuseFailAlloc_380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_377_ = l_Lake_instReprDynlib_repr___redArg(v_head_370_);
                v___x_378_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_378_, 0, v___x_376_);
                lean_ctor_set(v___x_378_, 1, v___x_377_);
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
    mut v_x_382_: *mut LeanObject,
    mut v_prec_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = l_Lake_instReprDynlib_repr___redArg(v_x_382_);
    return v___x_384_;
}
pub unsafe fn l_Lake_instReprDynlib_repr___boxed(
    mut v_x_385_: *mut LeanObject,
    mut v_prec_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l_Lake_instReprDynlib_repr(v_x_385_, v_prec_386_);
    lean_dec(v_prec_386_);
    return v_res_387_;
}
pub unsafe fn l_Lake_Dynlib_dir_x3f(mut v_self_390_: *mut LeanObject) -> *mut LeanObject {
    let mut v_path_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v_path_391_ = lean_ctor_get(v_self_390_, 0);
    lean_inc_ref(v_path_391_);
    lean_dec_ref(v_self_390_);
    v___x_392_ = l_System_FilePath_parent(v_path_391_);
    return v___x_392_;
}
pub unsafe fn l_Lake_Dynlib_instToJson___lam__0(mut v_x_393_: *mut LeanObject) -> *mut LeanObject {
    let mut v_path_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v_path_394_ = lean_ctor_get(v_x_393_, 0);
    lean_inc_ref(v_path_394_);
    v___x_395_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_395_, 0, v_path_394_);
    return v___x_395_;
}
pub unsafe fn l_Lake_Dynlib_instToJson___lam__0___boxed(
    mut v_x_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_397_: *mut LeanObject = core::ptr::null_mut();
    v_res_397_ = l_Lake_Dynlib_instToJson___lam__0(v_x_396_);
    lean_dec_ref(v_x_396_);
    return v_res_397_;
}
pub unsafe fn l_Lake_Dynlib_instToString___lam__0(
    mut v_x_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_401_: *mut LeanObject = core::ptr::null_mut();
    v_path_401_ = lean_ctor_get(v_x_400_, 0);
    lean_inc_ref(v_path_401_);
    return v_path_401_;
}
pub unsafe fn l_Lake_Dynlib_instToString___lam__0___boxed(
    mut v_x_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_403_: *mut LeanObject = core::ptr::null_mut();
    v_res_403_ = l_Lake_Dynlib_instToString___lam__0(v_x_402_);
    lean_dec_ref(v_x_402_);
    return v_res_403_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Dynlib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_OutFormat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Dynlib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Dynlib(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_OutFormat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_Dynlib(builtin);
}
