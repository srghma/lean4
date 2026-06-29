// Lean compiler output
// Module: Lean.Data.Lsp.Window
// Imports: Lean.Data.Json.FromToJson.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, l_Option_fromJson_x3f___redArg,
    l_Option_toJson___redArg, runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{lean_array_to_list, lean_nat_dec_eq};
pub static l_instFromJsonMessageType___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
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
        85, 110, 107, 110, 111, 119, 110, 32, 77, 101, 115, 115, 97, 103, 101, 84, 121, 112, 101,
        32, 73, 68, 0,
    ],
};
static mut l_instFromJsonMessageType___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageType___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instFromJsonMessageType___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonMessageType___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonMessageType___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonMessageType___lam__0___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instFromJsonMessageType___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageType___lam__0___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instFromJsonMessageType___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageType___lam__0___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instFromJsonMessageType___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageType___lam__0___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
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
static mut l_instFromJsonMessageType___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instFromJsonMessageType___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFromJsonMessageType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instFromJsonMessageType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_instToJsonMessageType___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instToJsonMessageType___lam__0___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instToJsonMessageType___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instToJsonMessageType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToJsonMessageType___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToJsonMessageType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonMessageType___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instToJsonMessageType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonMessageType___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageParams_fromJson___closed__0_value:
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
    m_data: [116, 121, 112, 101, 0],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageParams_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        83, 104, 111, 119, 77, 101, 115, 115, 97, 103, 101, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageParams_fromJson___closed__2_value:
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
        core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1980751476741436956 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageParams_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonShowMessageParams_fromJson___closed__4_value:
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
    m_data: [46, 0],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageParams_fromJson___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonShowMessageParams_fromJson___closed__6_value:
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
        core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11503787708459150704 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageParams_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instFromJsonShowMessageParams_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonShowMessageParams_fromJson___closed__9_value:
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
    m_data: [58, 32, 0],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageParams_fromJson___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonShowMessageParams_fromJson___closed__11_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 101, 115, 115, 97, 103, 101, 0],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageParams_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__11_value)
            as *mut crate::leanh::LeanObject,
        982637797389909653 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonShowMessageParams_fromJson___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageParams_fromJson___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instFromJsonShowMessageParams_fromJson___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instFromJsonShowMessageParams_fromJson___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonShowMessageParams_fromJson___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonShowMessageParams___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instFromJsonShowMessageParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFromJsonShowMessageParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instFromJsonShowMessageParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToJsonShowMessageParams_toJson___closed__0_value: crate::leanh::LeanArrayObject<
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
static mut l_instToJsonShowMessageParams_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageParams_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToJsonShowMessageParams___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToJsonShowMessageParams_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToJsonShowMessageParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instToJsonShowMessageParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageActionItem_fromJson___closed__0_value:
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
    m_data: [116, 105, 116, 108, 101, 0],
};
static mut l_instFromJsonMessageActionItem_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageActionItem_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageActionItem_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        77, 101, 115, 115, 97, 103, 101, 65, 99, 116, 105, 111, 110, 73, 116, 101, 109, 0,
    ],
};
static mut l_instFromJsonMessageActionItem_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageActionItem_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonMessageActionItem_fromJson___closed__2_value:
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
        core::ptr::addr_of!(l_instFromJsonMessageActionItem_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        3890167835572490881 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonMessageActionItem_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageActionItem_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonMessageActionItem_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonMessageActionItem_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instFromJsonMessageActionItem_fromJson___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonMessageActionItem_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonMessageActionItem_fromJson___closed__5_value:
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
        core::ptr::addr_of!(l_instFromJsonMessageActionItem_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14590743692222096379 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonMessageActionItem_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageActionItem_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonMessageActionItem_fromJson___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonMessageActionItem_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instFromJsonMessageActionItem_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonMessageActionItem_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instFromJsonMessageActionItem_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instFromJsonMessageActionItem_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instFromJsonMessageActionItem___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instFromJsonMessageActionItem_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFromJsonMessageActionItem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageActionItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instFromJsonMessageActionItem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonMessageActionItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToJsonMessageActionItem___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instToJsonMessageActionItem_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToJsonMessageActionItem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonMessageActionItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instToJsonMessageActionItem: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonMessageActionItem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageRequestParams_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
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
        83, 104, 111, 119, 77, 101, 115, 115, 97, 103, 101, 82, 101, 113, 117, 101, 115, 116, 80,
        97, 114, 97, 109, 115, 0,
    ],
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageRequestParams_fromJson___closed__1_value:
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
        core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15625569191833738362 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instFromJsonShowMessageRequestParams_fromJson___closed__8_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 99, 116, 105, 111, 110, 115, 0],
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageRequestParams_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 99, 116, 105, 111, 110, 115, 63, 0],
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageRequestParams_fromJson___closed__10_value:
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
        core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__9_value)
            as *mut crate::leanh::LeanObject,
        6577422343849019359 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_instFromJsonShowMessageRequestParams_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instFromJsonShowMessageRequestParams___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instFromJsonShowMessageRequestParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instFromJsonShowMessageRequestParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instFromJsonShowMessageRequestParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageRequestParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToJsonShowMessageRequestParams___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_instToJsonShowMessageRequestParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instToJsonShowMessageRequestParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageRequestParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instToJsonShowMessageRequestParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageRequestParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00instFromJsonShowMessageResponse_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00instFromJsonShowMessageResponse_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00instFromJsonShowMessageResponse_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_instFromJsonShowMessageResponse___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_fromJson_x3f___at___00instFromJsonShowMessageResponse_spec__0
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFromJsonShowMessageResponse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageResponse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instFromJsonShowMessageResponse: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFromJsonShowMessageResponse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instToJsonShowMessageResponse___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_toJson___at___00instToJsonShowMessageResponse_spec__0
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToJsonShowMessageResponse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageResponse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instToJsonShowMessageResponse: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToJsonShowMessageResponse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_MessageType_ctorIdx(mut v_x_655_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_655_ {
        0 => {
            let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_656_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_656_;
        }
        1 => {
            let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_657_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_657_;
        }
        2 => {
            let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_658_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_658_;
        }
        _ => {
            let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_659_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_659_;
        }
    }
}
pub unsafe fn l_MessageType_ctorIdx___boxed(
    mut v_x_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_661_: u8 = 0;
    let mut v_res_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_661_ = (crate::leanh::lean_unbox(v_x_660_) as u8);
    v_res_662_ = l_MessageType_ctorIdx(v_x_boxed_661_);
    return v_res_662_;
}
pub unsafe fn l_MessageType_toCtorIdx(mut v_x_663_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_664_ = l_MessageType_ctorIdx(v_x_663_);
    return v___x_664_;
}
pub unsafe fn l_MessageType_toCtorIdx___boxed(
    mut v_x_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_666_: u8 = 0;
    let mut v_res_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_666_ = (crate::leanh::lean_unbox(v_x_665_) as u8);
    v_res_667_ = l_MessageType_toCtorIdx(v_x_4__boxed_666_);
    return v_res_667_;
}
pub unsafe fn l_MessageType_ctorElim___redArg(
    mut v_k_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_668_);
    return v_k_668_;
}
pub unsafe fn l_MessageType_ctorElim___redArg___boxed(
    mut v_k_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_MessageType_ctorElim___redArg(v_k_669_);
    crate::leanh::lean_dec(v_k_669_);
    return v_res_670_;
}
pub unsafe fn l_MessageType_ctorElim(
    mut v_motive_671_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_672_: *mut crate::leanh::LeanObject,
    mut v_t_673_: u8,
    mut v_h_674_: *mut crate::leanh::LeanObject,
    mut v_k_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_675_);
    return v_k_675_;
}
pub unsafe fn l_MessageType_ctorElim___boxed(
    mut v_motive_676_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_677_: *mut crate::leanh::LeanObject,
    mut v_t_678_: *mut crate::leanh::LeanObject,
    mut v_h_679_: *mut crate::leanh::LeanObject,
    mut v_k_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_681_: u8 = 0;
    let mut v_res_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_681_ = (crate::leanh::lean_unbox(v_t_678_) as u8);
    v_res_682_ = l_MessageType_ctorElim(
        v_motive_676_,
        v_ctorIdx_677_,
        v_t_boxed_681_,
        v_h_679_,
        v_k_680_,
    );
    crate::leanh::lean_dec(v_k_680_);
    crate::leanh::lean_dec(v_ctorIdx_677_);
    return v_res_682_;
}
pub unsafe fn l_MessageType_error_elim___redArg(
    mut v_error_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_error_683_);
    return v_error_683_;
}
pub unsafe fn l_MessageType_error_elim___redArg___boxed(
    mut v_error_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_685_ = l_MessageType_error_elim___redArg(v_error_684_);
    crate::leanh::lean_dec(v_error_684_);
    return v_res_685_;
}
pub unsafe fn l_MessageType_error_elim(
    mut v_motive_686_: *mut crate::leanh::LeanObject,
    mut v_t_687_: u8,
    mut v_h_688_: *mut crate::leanh::LeanObject,
    mut v_error_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_error_689_);
    return v_error_689_;
}
pub unsafe fn l_MessageType_error_elim___boxed(
    mut v_motive_690_: *mut crate::leanh::LeanObject,
    mut v_t_691_: *mut crate::leanh::LeanObject,
    mut v_h_692_: *mut crate::leanh::LeanObject,
    mut v_error_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_694_: u8 = 0;
    let mut v_res_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_694_ = (crate::leanh::lean_unbox(v_t_691_) as u8);
    v_res_695_ = l_MessageType_error_elim(v_motive_690_, v_t_boxed_694_, v_h_692_, v_error_693_);
    crate::leanh::lean_dec(v_error_693_);
    return v_res_695_;
}
pub unsafe fn l_MessageType_warning_elim___redArg(
    mut v_warning_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_warning_696_);
    return v_warning_696_;
}
pub unsafe fn l_MessageType_warning_elim___redArg___boxed(
    mut v_warning_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_698_ = l_MessageType_warning_elim___redArg(v_warning_697_);
    crate::leanh::lean_dec(v_warning_697_);
    return v_res_698_;
}
pub unsafe fn l_MessageType_warning_elim(
    mut v_motive_699_: *mut crate::leanh::LeanObject,
    mut v_t_700_: u8,
    mut v_h_701_: *mut crate::leanh::LeanObject,
    mut v_warning_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_warning_702_);
    return v_warning_702_;
}
pub unsafe fn l_MessageType_warning_elim___boxed(
    mut v_motive_703_: *mut crate::leanh::LeanObject,
    mut v_t_704_: *mut crate::leanh::LeanObject,
    mut v_h_705_: *mut crate::leanh::LeanObject,
    mut v_warning_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_707_: u8 = 0;
    let mut v_res_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_707_ = (crate::leanh::lean_unbox(v_t_704_) as u8);
    v_res_708_ =
        l_MessageType_warning_elim(v_motive_703_, v_t_boxed_707_, v_h_705_, v_warning_706_);
    crate::leanh::lean_dec(v_warning_706_);
    return v_res_708_;
}
pub unsafe fn l_MessageType_info_elim___redArg(
    mut v_info_709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_info_709_);
    return v_info_709_;
}
pub unsafe fn l_MessageType_info_elim___redArg___boxed(
    mut v_info_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_711_ = l_MessageType_info_elim___redArg(v_info_710_);
    crate::leanh::lean_dec(v_info_710_);
    return v_res_711_;
}
pub unsafe fn l_MessageType_info_elim(
    mut v_motive_712_: *mut crate::leanh::LeanObject,
    mut v_t_713_: u8,
    mut v_h_714_: *mut crate::leanh::LeanObject,
    mut v_info_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_info_715_);
    return v_info_715_;
}
pub unsafe fn l_MessageType_info_elim___boxed(
    mut v_motive_716_: *mut crate::leanh::LeanObject,
    mut v_t_717_: *mut crate::leanh::LeanObject,
    mut v_h_718_: *mut crate::leanh::LeanObject,
    mut v_info_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_720_: u8 = 0;
    let mut v_res_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_720_ = (crate::leanh::lean_unbox(v_t_717_) as u8);
    v_res_721_ = l_MessageType_info_elim(v_motive_716_, v_t_boxed_720_, v_h_718_, v_info_719_);
    crate::leanh::lean_dec(v_info_719_);
    return v_res_721_;
}
pub unsafe fn l_MessageType_log_elim___redArg(
    mut v_log_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_log_722_);
    return v_log_722_;
}
pub unsafe fn l_MessageType_log_elim___redArg___boxed(
    mut v_log_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_MessageType_log_elim___redArg(v_log_723_);
    crate::leanh::lean_dec(v_log_723_);
    return v_res_724_;
}
pub unsafe fn l_MessageType_log_elim(
    mut v_motive_725_: *mut crate::leanh::LeanObject,
    mut v_t_726_: u8,
    mut v_h_727_: *mut crate::leanh::LeanObject,
    mut v_log_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_log_728_);
    return v_log_728_;
}
pub unsafe fn l_MessageType_log_elim___boxed(
    mut v_motive_729_: *mut crate::leanh::LeanObject,
    mut v_t_730_: *mut crate::leanh::LeanObject,
    mut v_h_731_: *mut crate::leanh::LeanObject,
    mut v_log_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_733_: u8 = 0;
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_733_ = (crate::leanh::lean_unbox(v_t_730_) as u8);
    v_res_734_ = l_MessageType_log_elim(v_motive_729_, v_t_boxed_733_, v_h_731_, v_log_732_);
    crate::leanh::lean_dec(v_log_732_);
    return v_res_734_;
}
pub unsafe fn _init_l_instFromJsonMessageType___lam__0___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v_natZero_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_738_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_739_ = lean_nat_to_int(v_natZero_738_);
    return v_intZero_739_;
}
pub unsafe fn l_instFromJsonMessageType___lam__0(
    mut v_x_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_760_: u8 = 0;
    let mut v_a_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: u8 = 0;
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u8 = 0;
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: u8 = 0;
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: u8 = 0;
    let mut v___x_770_: u8 = 0;
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: u8 = 0;
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_752_) == 2 {
                    v_n_755_ = crate::leanh::lean_ctor_get(v_x_752_, 0);
                    v_mantissa_756_ = crate::leanh::lean_ctor_get(v_n_755_, 0);
                    v_exponent_757_ = crate::leanh::lean_ctor_get(v_n_755_, 1);
                    v_natZero_758_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_intZero_759_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_instFromJsonMessageType___lam__0___closed__2),
                        core::ptr::addr_of_mut!(
                            l_instFromJsonMessageType___lam__0___closed__2_once
                        ),
                        _init_l_instFromJsonMessageType___lam__0___closed__2,
                    );
                    v_isNeg_760_ = lean_int_dec_lt(v_mantissa_756_, v_intZero_759_);
                    if v_isNeg_760_ == 0 {
                        v_a_761_ = lean_nat_abs(v_mantissa_756_);
                        v___x_762_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_763_ = lean_nat_dec_eq(v_a_761_, v___x_762_);
                        if v___x_763_ == 0 {
                            v___x_764_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_765_ = lean_nat_dec_eq(v_a_761_, v___x_764_);
                            if v___x_765_ == 0 {
                                v___x_766_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_767_ = lean_nat_dec_eq(v_a_761_, v___x_766_);
                                if v___x_767_ == 0 {
                                    v___x_768_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_769_ = lean_nat_dec_eq(v_a_761_, v___x_768_);
                                    crate::leanh::lean_dec(v_a_761_);
                                    if v___x_769_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_770_ =
                                            lean_nat_dec_eq(v_exponent_757_, v_natZero_758_);
                                        if v___x_770_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_771_ =
                                                l_instFromJsonMessageType___lam__0___closed__3;
                                            return v___x_771_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_761_);
                                    v___x_772_ = lean_nat_dec_eq(v_exponent_757_, v_natZero_758_);
                                    if v___x_772_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_773_ = l_instFromJsonMessageType___lam__0___closed__4;
                                        return v___x_773_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_761_);
                                v___x_774_ = lean_nat_dec_eq(v_exponent_757_, v_natZero_758_);
                                if v___x_774_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_775_ = l_instFromJsonMessageType___lam__0___closed__5;
                                    return v___x_775_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_761_);
                            v___x_776_ = lean_nat_dec_eq(v_exponent_757_, v_natZero_758_);
                            if v___x_776_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_777_ = l_instFromJsonMessageType___lam__0___closed__6;
                                return v___x_777_;
                            }
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_754_ = l_instFromJsonMessageType___lam__0___closed__1;
                return v___x_754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instFromJsonMessageType___lam__0___boxed(
    mut v_x_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_779_ = l_instFromJsonMessageType___lam__0(v_x_778_);
    crate::leanh::lean_dec(v_x_778_);
    return v_res_779_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_782_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_783_ = l_Lean_JsonNumber_fromNat(v___x_782_);
    return v___x_783_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__0_once),
        _init_l_instToJsonMessageType___lam__0___closed__0,
    );
    v___x_785_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_785_, 0, v___x_784_);
    return v___x_785_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_787_ = l_Lean_JsonNumber_fromNat(v___x_786_);
    return v___x_787_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_788_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__2_once),
        _init_l_instToJsonMessageType___lam__0___closed__2,
    );
    v___x_789_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_789_, 0, v___x_788_);
    return v___x_789_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_791_ = l_Lean_JsonNumber_fromNat(v___x_790_);
    return v___x_791_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__4_once),
        _init_l_instToJsonMessageType___lam__0___closed__4,
    );
    v___x_793_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_792_);
    return v___x_793_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_795_ = l_Lean_JsonNumber_fromNat(v___x_794_);
    return v___x_795_;
}
pub unsafe fn _init_l_instToJsonMessageType___lam__0___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__6_once),
        _init_l_instToJsonMessageType___lam__0___closed__6,
    );
    v___x_797_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_796_);
    return v___x_797_;
}
pub unsafe fn l_instToJsonMessageType___lam__0(mut v_x_798_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_798_ {
        0 => {
            let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_799_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__1),
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__1_once),
                _init_l_instToJsonMessageType___lam__0___closed__1,
            );
            return v___x_799_;
        }
        1 => {
            let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_800_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__3),
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__3_once),
                _init_l_instToJsonMessageType___lam__0___closed__3,
            );
            return v___x_800_;
        }
        2 => {
            let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_801_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__5),
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__5_once),
                _init_l_instToJsonMessageType___lam__0___closed__5,
            );
            return v___x_801_;
        }
        _ => {
            let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_802_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__7),
                core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__7_once),
                _init_l_instToJsonMessageType___lam__0___closed__7,
            );
            return v___x_802_;
        }
    }
}
pub unsafe fn l_instToJsonMessageType___lam__0___boxed(
    mut v_x_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_106__boxed_804_: u8 = 0;
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_106__boxed_804_ = (crate::leanh::lean_unbox(v_x_803_) as u8);
    v_res_805_ = l_instToJsonMessageType___lam__0(v_x_106__boxed_804_);
    return v_res_805_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(
    mut v_j_808_: *mut crate::leanh::LeanObject,
    mut v_k_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_818_: u8 = 0;
    let mut v_a_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: u8 = 0;
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_812_ = l_Lean_Json_getObjValD(v_j_808_, v_k_809_);
                if crate::leanh::lean_obj_tag(v___x_812_) == 2 {
                    v_n_813_ = crate::leanh::lean_ctor_get(v___x_812_, 0);
                    crate::leanh::lean_inc_ref(v_n_813_);
                    crate::leanh::lean_dec_ref_known(v___x_812_, 1);
                    v_mantissa_814_ = crate::leanh::lean_ctor_get(v_n_813_, 0);
                    crate::leanh::lean_inc(v_mantissa_814_);
                    v_exponent_815_ = crate::leanh::lean_ctor_get(v_n_813_, 1);
                    crate::leanh::lean_inc(v_exponent_815_);
                    crate::leanh::lean_dec_ref(v_n_813_);
                    v_natZero_816_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_intZero_817_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_instFromJsonMessageType___lam__0___closed__2),
                        core::ptr::addr_of_mut!(
                            l_instFromJsonMessageType___lam__0___closed__2_once
                        ),
                        _init_l_instFromJsonMessageType___lam__0___closed__2,
                    );
                    v_isNeg_818_ = lean_int_dec_lt(v_mantissa_814_, v_intZero_817_);
                    if v_isNeg_818_ == 0 {
                        v_a_819_ = lean_nat_abs(v_mantissa_814_);
                        crate::leanh::lean_dec(v_mantissa_814_);
                        v___x_820_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_821_ = lean_nat_dec_eq(v_a_819_, v___x_820_);
                        if v___x_821_ == 0 {
                            v___x_822_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_823_ = lean_nat_dec_eq(v_a_819_, v___x_822_);
                            if v___x_823_ == 0 {
                                v___x_824_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_825_ = lean_nat_dec_eq(v_a_819_, v___x_824_);
                                if v___x_825_ == 0 {
                                    v___x_826_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_827_ = lean_nat_dec_eq(v_a_819_, v___x_826_);
                                    crate::leanh::lean_dec(v_a_819_);
                                    if v___x_827_ == 0 {
                                        crate::leanh::lean_dec(v_exponent_815_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_828_ =
                                            lean_nat_dec_eq(v_exponent_815_, v_natZero_816_);
                                        crate::leanh::lean_dec(v_exponent_815_);
                                        if v___x_828_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_829_ =
                                                l_instFromJsonMessageType___lam__0___closed__3;
                                            return v___x_829_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_819_);
                                    v___x_830_ = lean_nat_dec_eq(v_exponent_815_, v_natZero_816_);
                                    crate::leanh::lean_dec(v_exponent_815_);
                                    if v___x_830_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_831_ = l_instFromJsonMessageType___lam__0___closed__4;
                                        return v___x_831_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_819_);
                                v___x_832_ = lean_nat_dec_eq(v_exponent_815_, v_natZero_816_);
                                crate::leanh::lean_dec(v_exponent_815_);
                                if v___x_832_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_833_ = l_instFromJsonMessageType___lam__0___closed__5;
                                    return v___x_833_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_819_);
                            v___x_834_ = lean_nat_dec_eq(v_exponent_815_, v_natZero_816_);
                            crate::leanh::lean_dec(v_exponent_815_);
                            if v___x_834_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_835_ = l_instFromJsonMessageType___lam__0___closed__6;
                                return v___x_835_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_exponent_815_);
                        crate::leanh::lean_dec(v_mantissa_814_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_812_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_811_ = l_instFromJsonMessageType___lam__0___closed__1;
                return v___x_811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0___boxed(
    mut v_j_836_: *mut crate::leanh::LeanObject,
    mut v_k_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ =
        l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(
            v_j_836_, v_k_837_,
        );
    crate::leanh::lean_dec_ref(v_k_837_);
    return v_res_838_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(
    mut v_j_839_: *mut crate::leanh::LeanObject,
    mut v_k_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = l_Lean_Json_getObjValD(v_j_839_, v_k_840_);
    v___x_842_ = l_Lean_Json_getStr_x3f(v___x_841_);
    return v___x_842_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1___boxed(
    mut v_j_843_: *mut crate::leanh::LeanObject,
    mut v_k_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ =
        l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(
            v_j_843_, v_k_844_,
        );
    crate::leanh::lean_dec_ref(v_k_844_);
    return v_res_845_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_850_ = 1;
    v___x_851_ = l_instFromJsonShowMessageParams_fromJson___closed__2;
    v___x_852_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_851_, v___x_850_);
    return v___x_852_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l_instFromJsonShowMessageParams_fromJson___closed__4;
    v___x_855_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__3_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__3,
    );
    v___x_856_ = lean_string_append(v___x_855_, v___x_854_);
    return v___x_856_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = 1;
    v___x_860_ = l_instFromJsonShowMessageParams_fromJson___closed__6;
    v___x_861_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_860_, v___x_859_);
    return v___x_861_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__7_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__7,
    );
    v___x_863_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__5_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__5,
    );
    v___x_864_ = lean_string_append(v___x_863_, v___x_862_);
    return v___x_864_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_instFromJsonShowMessageParams_fromJson___closed__9;
    v___x_867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__8_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__8,
    );
    v___x_868_ = lean_string_append(v___x_867_, v___x_866_);
    return v___x_868_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = 1;
    v___x_873_ = l_instFromJsonShowMessageParams_fromJson___closed__12;
    v___x_874_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__13_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__13,
    );
    v___x_876_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__5_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__5,
    );
    v___x_877_ = lean_string_append(v___x_876_, v___x_875_);
    return v___x_877_;
}
pub unsafe fn _init_l_instFromJsonShowMessageParams_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ = l_instFromJsonShowMessageParams_fromJson___closed__9;
    v___x_879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__14_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__14,
    );
    v___x_880_ = lean_string_append(v___x_879_, v___x_878_);
    return v___x_880_;
}
pub unsafe fn l_instFromJsonShowMessageParams_fromJson(
    mut v_json_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_a_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut v_a_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut v_a_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_926_: u8 = 0;
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_882_ = l_instFromJsonShowMessageParams_fromJson___closed__0;
                crate::leanh::lean_inc(v_json_881_);
                v___x_883_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(v_json_881_, v___x_882_);
                if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                    crate::leanh::lean_dec(v_json_881_);
                    v_a_884_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                    v_isSharedCheck_893_ = (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                    if v_isSharedCheck_893_ == 0 {
                        v___x_886_ = v___x_883_;
                        v_isShared_887_ = v_isSharedCheck_893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_884_);
                        crate::leanh::lean_dec(v___x_883_);
                        v___x_886_ = crate::leanh::lean_box(0);
                        v_isShared_887_ = v_isSharedCheck_893_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                        crate::leanh::lean_dec(v_json_881_);
                        v_a_894_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_901_ = (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_901_ == 0 {
                            v___x_896_ = v___x_883_;
                            v_isShared_897_ = v_isSharedCheck_901_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_894_);
                            crate::leanh::lean_dec(v___x_883_);
                            v___x_896_ = crate::leanh::lean_box(0);
                            v_isShared_897_ = v_isSharedCheck_901_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_902_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        crate::leanh::lean_inc(v_a_902_);
                        crate::leanh::lean_dec_ref_known(v___x_883_, 1);
                        v___x_903_ = l_instFromJsonShowMessageParams_fromJson___closed__11;
                        v___x_904_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_json_881_, v___x_903_);
                        if crate::leanh::lean_obj_tag(v___x_904_) == 0 {
                            crate::leanh::lean_dec(v_a_902_);
                            v_a_905_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                            v_isSharedCheck_914_ =
                                (!crate::leanh::lean_is_exclusive(v___x_904_)) as u8;
                            if v_isSharedCheck_914_ == 0 {
                                v___x_907_ = v___x_904_;
                                v_isShared_908_ = v_isSharedCheck_914_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_905_);
                                crate::leanh::lean_dec(v___x_904_);
                                v___x_907_ = crate::leanh::lean_box(0);
                                v_isShared_908_ = v_isSharedCheck_914_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_904_) == 0 {
                                crate::leanh::lean_dec(v_a_902_);
                                v_a_915_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                                v_isSharedCheck_922_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_904_)) as u8;
                                if v_isSharedCheck_922_ == 0 {
                                    v___x_917_ = v___x_904_;
                                    v_isShared_918_ = v_isSharedCheck_922_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_915_);
                                    crate::leanh::lean_dec(v___x_904_);
                                    v___x_917_ = crate::leanh::lean_box(0);
                                    v_isShared_918_ = v_isSharedCheck_922_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_923_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                                v_isSharedCheck_932_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_904_)) as u8;
                                if v_isSharedCheck_932_ == 0 {
                                    v___x_925_ = v___x_904_;
                                    v_isShared_926_ = v_isSharedCheck_932_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_923_);
                                    crate::leanh::lean_dec(v___x_904_);
                                    v___x_925_ = crate::leanh::lean_box(0);
                                    v_isShared_926_ = v_isSharedCheck_932_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_888_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__10),
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageParams_fromJson___closed__10_once
                    ),
                    _init_l_instFromJsonShowMessageParams_fromJson___closed__10,
                );
                v___x_889_ = lean_string_append(v___x_888_, v_a_884_);
                crate::leanh::lean_dec(v_a_884_);
                if v_isShared_887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_886_, 0, v___x_889_);
                    v___x_891_ = v___x_886_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
                    v___x_891_ = v_reuseFailAlloc_892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_891_;
            }
            3 => {
                if v_isShared_897_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_896_, 0);
                    v___x_899_ = v___x_896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_899_;
            }
            5 => {
                v___x_909_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__15),
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageParams_fromJson___closed__15_once
                    ),
                    _init_l_instFromJsonShowMessageParams_fromJson___closed__15,
                );
                v___x_910_ = lean_string_append(v___x_909_, v_a_905_);
                crate::leanh::lean_dec(v_a_905_);
                if v_isShared_908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_907_, 0, v___x_910_);
                    v___x_912_ = v___x_907_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
                    v___x_912_ = v_reuseFailAlloc_913_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_912_;
            }
            7 => {
                if v_isShared_918_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_917_, 0);
                    v___x_920_ = v___x_917_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
                    v___x_920_ = v_reuseFailAlloc_921_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_920_;
            }
            9 => {
                v___x_927_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_927_, 0, v_a_923_);
                v___x_928_ = (crate::leanh::lean_unbox(v_a_902_) as u8);
                crate::leanh::lean_dec(v_a_902_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_928_,
                );
                if v_isShared_926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_925_, 0, v___x_927_);
                    v___x_930_ = v___x_925_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_927_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_935_) == 0 {
                    v___x_937_ = lean_array_to_list(v_a_936_);
                    return v___x_937_;
                } else {
                    v_head_938_ = crate::leanh::lean_ctor_get(v_a_935_, 0);
                    crate::leanh::lean_inc(v_head_938_);
                    v_tail_939_ = crate::leanh::lean_ctor_get(v_a_935_, 1);
                    crate::leanh::lean_inc(v_tail_939_);
                    crate::leanh::lean_dec_ref_known(v_a_935_, 2);
                    v___x_940_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_936_,
                        v_head_938_,
                    );
                    v_a_935_ = v_tail_939_;
                    v_a_936_ = v___x_940_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToJsonShowMessageParams_toJson(
    mut v_x_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_945_: u8 = 0;
    let mut v_message_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_945_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_944_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_message_946_ = crate::leanh::lean_ctor_get(v_x_944_, 0);
                v___x_947_ = l_instFromJsonShowMessageParams_fromJson___closed__0;
                match v_type_945_ {
                    0 => {
                        v___x_962_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__1_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__1,
                        );
                        v___y_949_ = v___x_962_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_963_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__3),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__3_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__3,
                        );
                        v___y_949_ = v___x_963_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_964_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__5),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__5_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__5,
                        );
                        v___y_949_ = v___x_964_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_965_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__7),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__7_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__7,
                        );
                        v___y_949_ = v___x_965_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_949_);
                v___x_950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_947_);
                crate::leanh::lean_ctor_set(v___x_950_, 1, v___y_949_);
                v___x_951_ = crate::leanh::lean_box(0);
                v___x_952_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_952_, 0, v___x_950_);
                crate::leanh::lean_ctor_set(v___x_952_, 1, v___x_951_);
                v___x_953_ = l_instFromJsonShowMessageParams_fromJson___closed__11;
                crate::leanh::lean_inc_ref(v_message_946_);
                v___x_954_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_954_, 0, v_message_946_);
                v___x_955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_955_, 0, v___x_953_);
                crate::leanh::lean_ctor_set(v___x_955_, 1, v___x_954_);
                v___x_956_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_956_, 0, v___x_955_);
                crate::leanh::lean_ctor_set(v___x_956_, 1, v___x_951_);
                v___x_957_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_957_, 0, v___x_956_);
                crate::leanh::lean_ctor_set(v___x_957_, 1, v___x_951_);
                v___x_958_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_958_, 0, v___x_952_);
                crate::leanh::lean_ctor_set(v___x_958_, 1, v___x_957_);
                v___x_959_ = l_instToJsonShowMessageParams_toJson___closed__0;
                v___x_960_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(v___x_958_, v___x_959_);
                v___x_961_ = l_Lean_Json_mkObj(v___x_960_);
                crate::leanh::lean_dec(v___x_960_);
                return v___x_961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToJsonShowMessageParams_toJson___boxed(
    mut v_x_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l_instToJsonShowMessageParams_toJson(v_x_966_);
    crate::leanh::lean_dec_ref(v_x_966_);
    return v_res_967_;
}
pub unsafe fn _init_l_instFromJsonMessageActionItem_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = 1;
    v___x_975_ = l_instFromJsonMessageActionItem_fromJson___closed__2;
    v___x_976_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_975_, v___x_974_);
    return v___x_976_;
}
pub unsafe fn _init_l_instFromJsonMessageActionItem_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_977_ = l_instFromJsonShowMessageParams_fromJson___closed__4;
    v___x_978_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__3_once),
        _init_l_instFromJsonMessageActionItem_fromJson___closed__3,
    );
    v___x_979_ = lean_string_append(v___x_978_, v___x_977_);
    return v___x_979_;
}
pub unsafe fn _init_l_instFromJsonMessageActionItem_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = 1;
    v___x_983_ = l_instFromJsonMessageActionItem_fromJson___closed__5;
    v___x_984_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_983_, v___x_982_);
    return v___x_984_;
}
pub unsafe fn _init_l_instFromJsonMessageActionItem_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__6_once),
        _init_l_instFromJsonMessageActionItem_fromJson___closed__6,
    );
    v___x_986_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__4_once),
        _init_l_instFromJsonMessageActionItem_fromJson___closed__4,
    );
    v___x_987_ = lean_string_append(v___x_986_, v___x_985_);
    return v___x_987_;
}
pub unsafe fn _init_l_instFromJsonMessageActionItem_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l_instFromJsonShowMessageParams_fromJson___closed__9;
    v___x_989_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__7_once),
        _init_l_instFromJsonMessageActionItem_fromJson___closed__7,
    );
    v___x_990_ = lean_string_append(v___x_989_, v___x_988_);
    return v___x_990_;
}
pub unsafe fn l_instFromJsonMessageActionItem_fromJson(
    mut v_json_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_997_: u8 = 0;
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1003_: u8 = 0;
    let mut v_a_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1007_: u8 = 0;
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut v_a_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_992_ = l_instFromJsonMessageActionItem_fromJson___closed__0;
                v___x_993_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_json_991_, v___x_992_);
                if crate::leanh::lean_obj_tag(v___x_993_) == 0 {
                    v_a_994_ = crate::leanh::lean_ctor_get(v___x_993_, 0);
                    v_isSharedCheck_1003_ = (!crate::leanh::lean_is_exclusive(v___x_993_)) as u8;
                    if v_isSharedCheck_1003_ == 0 {
                        v___x_996_ = v___x_993_;
                        v_isShared_997_ = v_isSharedCheck_1003_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_994_);
                        crate::leanh::lean_dec(v___x_993_);
                        v___x_996_ = crate::leanh::lean_box(0);
                        v_isShared_997_ = v_isSharedCheck_1003_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_993_) == 0 {
                        v_a_1004_ = crate::leanh::lean_ctor_get(v___x_993_, 0);
                        v_isSharedCheck_1011_ =
                            (!crate::leanh::lean_is_exclusive(v___x_993_)) as u8;
                        if v_isSharedCheck_1011_ == 0 {
                            v___x_1006_ = v___x_993_;
                            v_isShared_1007_ = v_isSharedCheck_1011_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1004_);
                            crate::leanh::lean_dec(v___x_993_);
                            v___x_1006_ = crate::leanh::lean_box(0);
                            v_isShared_1007_ = v_isSharedCheck_1011_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1012_ = crate::leanh::lean_ctor_get(v___x_993_, 0);
                        v_isSharedCheck_1019_ =
                            (!crate::leanh::lean_is_exclusive(v___x_993_)) as u8;
                        if v_isSharedCheck_1019_ == 0 {
                            v___x_1014_ = v___x_993_;
                            v_isShared_1015_ = v_isSharedCheck_1019_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1012_);
                            crate::leanh::lean_dec(v___x_993_);
                            v___x_1014_ = crate::leanh::lean_box(0);
                            v_isShared_1015_ = v_isSharedCheck_1019_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_998_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_instFromJsonMessageActionItem_fromJson___closed__8),
                    core::ptr::addr_of_mut!(
                        l_instFromJsonMessageActionItem_fromJson___closed__8_once
                    ),
                    _init_l_instFromJsonMessageActionItem_fromJson___closed__8,
                );
                v___x_999_ = lean_string_append(v___x_998_, v_a_994_);
                crate::leanh::lean_dec(v_a_994_);
                if v_isShared_997_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_996_, 0, v___x_999_);
                    v___x_1001_ = v___x_996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
                    v___x_1001_ = v_reuseFailAlloc_1002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1001_;
            }
            3 => {
                if v_isShared_1007_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1006_, 0);
                    v___x_1009_ = v___x_1006_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
                    v___x_1009_ = v_reuseFailAlloc_1010_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1009_;
            }
            5 => {
                if v_isShared_1015_ == 0 {
                    v___x_1017_ = v___x_1014_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
                    v___x_1017_ = v_reuseFailAlloc_1018_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToJsonMessageActionItem_toJson(
    mut v_x_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_instFromJsonMessageActionItem_fromJson___closed__0;
    v___x_1024_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1024_, 0, v_x_1022_);
    v___x_1025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1025_, 0, v___x_1023_);
    crate::leanh::lean_ctor_set(v___x_1025_, 1, v___x_1024_);
    v___x_1026_ = crate::leanh::lean_box(0);
    v___x_1027_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1027_, 0, v___x_1025_);
    crate::leanh::lean_ctor_set(v___x_1027_, 1, v___x_1026_);
    v___x_1028_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1028_, 0, v___x_1027_);
    crate::leanh::lean_ctor_set(v___x_1028_, 1, v___x_1026_);
    v___x_1029_ = l_instToJsonShowMessageParams_toJson___closed__0;
    v___x_1030_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(v___x_1028_, v___x_1029_);
    v___x_1031_ = l_Lean_Json_mkObj(v___x_1030_);
    crate::leanh::lean_dec(v___x_1030_);
    return v___x_1031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(
    mut v_sz_1034_: usize,
    mut v_i_1035_: usize,
    mut v_bs_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1044_: u8 = 0;
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1048_: u8 = 0;
    let mut v_a_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: usize = 0;
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1037_ = lean_usize_dec_lt(v_i_1035_, v_sz_1034_);
                if v___x_1037_ == 0 {
                    v___x_1038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1038_, 0, v_bs_1036_);
                    return v___x_1038_;
                } else {
                    v_v_1039_ = lean_array_uget_borrowed(v_bs_1036_, v_i_1035_);
                    crate::leanh::lean_inc(v_v_1039_);
                    v___x_1040_ = l_instFromJsonMessageActionItem_fromJson(v_v_1039_);
                    if crate::leanh::lean_obj_tag(v___x_1040_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_1036_);
                        v_a_1041_ = crate::leanh::lean_ctor_get(v___x_1040_, 0);
                        v_isSharedCheck_1048_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1040_)) as u8;
                        if v_isSharedCheck_1048_ == 0 {
                            v___x_1043_ = v___x_1040_;
                            v_isShared_1044_ = v_isSharedCheck_1048_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1041_);
                            crate::leanh::lean_dec(v___x_1040_);
                            v___x_1043_ = crate::leanh::lean_box(0);
                            v_isShared_1044_ = v_isSharedCheck_1048_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1049_ = crate::leanh::lean_ctor_get(v___x_1040_, 0);
                        crate::leanh::lean_inc(v_a_1049_);
                        crate::leanh::lean_dec_ref_known(v___x_1040_, 1);
                        v___x_1050_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1051_ = lean_array_uset(v_bs_1036_, v_i_1035_, v___x_1050_);
                        v___x_1052_ = 1usize;
                        v___x_1053_ = lean_usize_add(v_i_1035_, v___x_1052_);
                        v___x_1054_ = lean_array_uset(v_bs_x27_1051_, v_i_1035_, v_a_1049_);
                        v_i_1035_ = v___x_1053_;
                        v_bs_1036_ = v___x_1054_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1044_ == 0 {
                    v___x_1046_ = v___x_1043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
                    v___x_1046_ = v_reuseFailAlloc_1047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_sz_1056_: *mut crate::leanh::LeanObject,
    mut v_i_1057_: *mut crate::leanh::LeanObject,
    mut v_bs_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1059_: usize = 0;
    let mut v_i_boxed_1060_: usize = 0;
    let mut v_res_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1059_ = crate::leanh::lean_unbox_usize(v_sz_1056_);
    crate::leanh::lean_dec(v_sz_1056_);
    v_i_boxed_1060_ = crate::leanh::lean_unbox_usize(v_i_1057_);
    crate::leanh::lean_dec(v_i_1057_);
    v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_1059_, v_i_boxed_1060_, v_bs_1058_);
    return v_res_1061_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(
    mut v_x_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1064_) == 4 {
        let mut v_elems_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1066_: usize = 0;
        let mut v___x_1067_: usize = 0;
        let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_1065_ = crate::leanh::lean_ctor_get(v_x_1064_, 0);
        crate::leanh::lean_inc_ref(v_elems_1065_);
        crate::leanh::lean_dec_ref_known(v_x_1064_, 1);
        v_sz_1066_ = lean_array_size(v_elems_1065_);
        v___x_1067_ = 0usize;
        v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_1066_, v___x_1067_, v_elems_1065_);
        return v___x_1068_;
    } else {
        let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1069_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0;
        v___x_1070_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_1071_ = l_Lean_Json_pretty(v_x_1064_, v___x_1070_);
        v___x_1072_ = lean_string_append(v___x_1069_, v___x_1071_);
        crate::leanh::lean_dec_ref(v___x_1071_);
        v___x_1073_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1;
        v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
        v___x_1075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
        return v___x_1075_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(
    mut v_x_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut v_a_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1092_: u8 = 0;
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1078_) == 0 {
                    v___x_1079_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0;
                    return v___x_1079_;
                } else {
                    v___x_1080_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(v_x_1078_);
                    if crate::leanh::lean_obj_tag(v___x_1080_) == 0 {
                        v_a_1081_ = crate::leanh::lean_ctor_get(v___x_1080_, 0);
                        v_isSharedCheck_1088_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1080_)) as u8;
                        if v_isSharedCheck_1088_ == 0 {
                            v___x_1083_ = v___x_1080_;
                            v_isShared_1084_ = v_isSharedCheck_1088_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1081_);
                            crate::leanh::lean_dec(v___x_1080_);
                            v___x_1083_ = crate::leanh::lean_box(0);
                            v_isShared_1084_ = v_isSharedCheck_1088_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1089_ = crate::leanh::lean_ctor_get(v___x_1080_, 0);
                        v_isSharedCheck_1097_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1080_)) as u8;
                        if v_isSharedCheck_1097_ == 0 {
                            v___x_1091_ = v___x_1080_;
                            v_isShared_1092_ = v_isSharedCheck_1097_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1089_);
                            crate::leanh::lean_dec(v___x_1080_);
                            v___x_1091_ = crate::leanh::lean_box(0);
                            v_isShared_1092_ = v_isSharedCheck_1097_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1084_ == 0 {
                    v___x_1086_ = v___x_1083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1086_;
            }
            3 => {
                v___x_1093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1093_, 0, v_a_1089_);
                if v_isShared_1092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1091_, 0, v___x_1093_);
                    v___x_1095_ = v___x_1091_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
                    v___x_1095_ = v_reuseFailAlloc_1096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(
    mut v_j_1098_: *mut crate::leanh::LeanObject,
    mut v_k_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = l_Lean_Json_getObjValD(v_j_1098_, v_k_1099_);
    v___x_1101_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(v___x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(
    mut v_j_1102_: *mut crate::leanh::LeanObject,
    mut v_k_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ =
        l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(
            v_j_1102_, v_k_1103_,
        );
    crate::leanh::lean_dec_ref(v_k_1103_);
    return v_res_1104_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = 1;
    v___x_1109_ = l_instFromJsonShowMessageRequestParams_fromJson___closed__1;
    v___x_1110_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1109_, v___x_1108_);
    return v___x_1110_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_instFromJsonShowMessageParams_fromJson___closed__4;
    v___x_1112_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__2_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__2,
    );
    v___x_1113_ = lean_string_append(v___x_1112_, v___x_1111_);
    return v___x_1113_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__7_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__7,
    );
    v___x_1115_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3,
    );
    v___x_1116_ = lean_string_append(v___x_1115_, v___x_1114_);
    return v___x_1116_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_instFromJsonShowMessageParams_fromJson___closed__9;
    v___x_1118_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__4_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__4,
    );
    v___x_1119_ = lean_string_append(v___x_1118_, v___x_1117_);
    return v___x_1119_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageParams_fromJson___closed__13_once),
        _init_l_instFromJsonShowMessageParams_fromJson___closed__13,
    );
    v___x_1121_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3,
    );
    v___x_1122_ = lean_string_append(v___x_1121_, v___x_1120_);
    return v___x_1122_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_instFromJsonShowMessageParams_fromJson___closed__9;
    v___x_1124_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__6_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__6,
    );
    v___x_1125_ = lean_string_append(v___x_1124_, v___x_1123_);
    return v___x_1125_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = 1;
    v___x_1131_ = l_instFromJsonShowMessageRequestParams_fromJson___closed__10;
    v___x_1132_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1131_, v___x_1130_);
    return v___x_1132_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__11),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__11_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__11,
    );
    v___x_1134_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3,
    );
    v___x_1135_ = lean_string_append(v___x_1134_, v___x_1133_);
    return v___x_1135_;
}
pub unsafe fn _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = l_instFromJsonShowMessageParams_fromJson___closed__9;
    v___x_1137_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_instFromJsonShowMessageRequestParams_fromJson___closed__12_once),
        _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__12,
    );
    v___x_1138_ = lean_string_append(v___x_1137_, v___x_1136_);
    return v___x_1138_;
}
pub unsafe fn l_instFromJsonShowMessageRequestParams_fromJson(
    mut v_json_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1145_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut v_a_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_a_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1172_: u8 = 0;
    let mut v_a_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1176_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut v_a_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1187_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1193_: u8 = 0;
    let mut v_a_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1197_: u8 = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_a_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1205_: u8 = 0;
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1140_ = l_instFromJsonShowMessageParams_fromJson___closed__0;
                crate::leanh::lean_inc(v_json_1139_);
                v___x_1141_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(v_json_1139_, v___x_1140_);
                if crate::leanh::lean_obj_tag(v___x_1141_) == 0 {
                    crate::leanh::lean_dec(v_json_1139_);
                    v_a_1142_ = crate::leanh::lean_ctor_get(v___x_1141_, 0);
                    v_isSharedCheck_1151_ = (!crate::leanh::lean_is_exclusive(v___x_1141_)) as u8;
                    if v_isSharedCheck_1151_ == 0 {
                        v___x_1144_ = v___x_1141_;
                        v_isShared_1145_ = v_isSharedCheck_1151_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1142_);
                        crate::leanh::lean_dec(v___x_1141_);
                        v___x_1144_ = crate::leanh::lean_box(0);
                        v_isShared_1145_ = v_isSharedCheck_1151_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1141_) == 0 {
                        crate::leanh::lean_dec(v_json_1139_);
                        v_a_1152_ = crate::leanh::lean_ctor_get(v___x_1141_, 0);
                        v_isSharedCheck_1159_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1141_)) as u8;
                        if v_isSharedCheck_1159_ == 0 {
                            v___x_1154_ = v___x_1141_;
                            v_isShared_1155_ = v_isSharedCheck_1159_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1152_);
                            crate::leanh::lean_dec(v___x_1141_);
                            v___x_1154_ = crate::leanh::lean_box(0);
                            v_isShared_1155_ = v_isSharedCheck_1159_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1160_ = crate::leanh::lean_ctor_get(v___x_1141_, 0);
                        crate::leanh::lean_inc(v_a_1160_);
                        crate::leanh::lean_dec_ref_known(v___x_1141_, 1);
                        v___x_1161_ = l_instFromJsonShowMessageParams_fromJson___closed__11;
                        crate::leanh::lean_inc(v_json_1139_);
                        v___x_1162_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_json_1139_, v___x_1161_);
                        if crate::leanh::lean_obj_tag(v___x_1162_) == 0 {
                            crate::leanh::lean_dec(v_a_1160_);
                            crate::leanh::lean_dec(v_json_1139_);
                            v_a_1163_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                            v_isSharedCheck_1172_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1162_)) as u8;
                            if v_isSharedCheck_1172_ == 0 {
                                v___x_1165_ = v___x_1162_;
                                v_isShared_1166_ = v_isSharedCheck_1172_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1163_);
                                crate::leanh::lean_dec(v___x_1162_);
                                v___x_1165_ = crate::leanh::lean_box(0);
                                v_isShared_1166_ = v_isSharedCheck_1172_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1162_) == 0 {
                                crate::leanh::lean_dec(v_a_1160_);
                                crate::leanh::lean_dec(v_json_1139_);
                                v_a_1173_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                                v_isSharedCheck_1180_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1162_)) as u8;
                                if v_isSharedCheck_1180_ == 0 {
                                    v___x_1175_ = v___x_1162_;
                                    v_isShared_1176_ = v_isSharedCheck_1180_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1173_);
                                    crate::leanh::lean_dec(v___x_1162_);
                                    v___x_1175_ = crate::leanh::lean_box(0);
                                    v_isShared_1176_ = v_isSharedCheck_1180_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1181_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                                crate::leanh::lean_inc(v_a_1181_);
                                crate::leanh::lean_dec_ref_known(v___x_1162_, 1);
                                v___x_1182_ =
                                    l_instFromJsonShowMessageRequestParams_fromJson___closed__8;
                                v___x_1183_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(v_json_1139_, v___x_1182_);
                                if crate::leanh::lean_obj_tag(v___x_1183_) == 0 {
                                    crate::leanh::lean_dec(v_a_1181_);
                                    crate::leanh::lean_dec(v_a_1160_);
                                    v_a_1184_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                                    v_isSharedCheck_1193_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1183_)) as u8;
                                    if v_isSharedCheck_1193_ == 0 {
                                        v___x_1186_ = v___x_1183_;
                                        v_isShared_1187_ = v_isSharedCheck_1193_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1184_);
                                        crate::leanh::lean_dec(v___x_1183_);
                                        v___x_1186_ = crate::leanh::lean_box(0);
                                        v_isShared_1187_ = v_isSharedCheck_1193_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_1183_) == 0 {
                                        crate::leanh::lean_dec(v_a_1181_);
                                        crate::leanh::lean_dec(v_a_1160_);
                                        v_a_1194_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                                        v_isSharedCheck_1201_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1183_)) as u8;
                                        if v_isSharedCheck_1201_ == 0 {
                                            v___x_1196_ = v___x_1183_;
                                            v_isShared_1197_ = v_isSharedCheck_1201_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1194_);
                                            crate::leanh::lean_dec(v___x_1183_);
                                            v___x_1196_ = crate::leanh::lean_box(0);
                                            v_isShared_1197_ = v_isSharedCheck_1201_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_1202_ = crate::leanh::lean_ctor_get(v___x_1183_, 0);
                                        v_isSharedCheck_1211_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1183_)) as u8;
                                        if v_isSharedCheck_1211_ == 0 {
                                            v___x_1204_ = v___x_1183_;
                                            v_isShared_1205_ = v_isSharedCheck_1211_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1202_);
                                            crate::leanh::lean_dec(v___x_1183_);
                                            v___x_1204_ = crate::leanh::lean_box(0);
                                            v_isShared_1205_ = v_isSharedCheck_1211_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1146_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageRequestParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageRequestParams_fromJson___closed__5_once
                    ),
                    _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__5,
                );
                v___x_1147_ = lean_string_append(v___x_1146_, v_a_1142_);
                crate::leanh::lean_dec(v_a_1142_);
                if v_isShared_1145_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1147_);
                    v___x_1149_ = v___x_1144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
                    v___x_1149_ = v_reuseFailAlloc_1150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1149_;
            }
            3 => {
                if v_isShared_1155_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1154_, 0);
                    v___x_1157_ = v___x_1154_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
                    v___x_1157_ = v_reuseFailAlloc_1158_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1157_;
            }
            5 => {
                v___x_1167_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageRequestParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageRequestParams_fromJson___closed__7_once
                    ),
                    _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__7,
                );
                v___x_1168_ = lean_string_append(v___x_1167_, v_a_1163_);
                crate::leanh::lean_dec(v_a_1163_);
                if v_isShared_1166_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1168_);
                    v___x_1170_ = v___x_1165_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
                    v___x_1170_ = v_reuseFailAlloc_1171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1170_;
            }
            7 => {
                if v_isShared_1176_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1175_, 0);
                    v___x_1178_ = v___x_1175_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1178_;
            }
            9 => {
                v___x_1188_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageRequestParams_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_instFromJsonShowMessageRequestParams_fromJson___closed__13_once
                    ),
                    _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__13,
                );
                v___x_1189_ = lean_string_append(v___x_1188_, v_a_1184_);
                crate::leanh::lean_dec(v_a_1184_);
                if v_isShared_1187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1189_);
                    v___x_1191_ = v___x_1186_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1192_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
                    v___x_1191_ = v_reuseFailAlloc_1192_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1191_;
            }
            11 => {
                if v_isShared_1197_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1196_, 0);
                    v___x_1199_ = v___x_1196_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
                    v___x_1199_ = v_reuseFailAlloc_1200_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1199_;
            }
            13 => {
                v___x_1206_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1206_, 0, v_a_1181_);
                crate::leanh::lean_ctor_set(v___x_1206_, 1, v_a_1202_);
                v___x_1207_ = (crate::leanh::lean_unbox(v_a_1160_) as u8);
                crate::leanh::lean_dec(v_a_1160_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1206_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1207_,
                );
                if v_isShared_1205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1204_, 0, v___x_1206_);
                    v___x_1209_ = v___x_1204_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
                    v___x_1209_ = v_reuseFailAlloc_1210_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(
    mut v_sz_1214_: usize,
    mut v_i_1215_: usize,
    mut v_bs_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: u8 = 0;
    let mut v_v_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: usize = 0;
    let mut v___x_1223_: usize = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1217_ = lean_usize_dec_lt(v_i_1215_, v_sz_1214_);
                if v___x_1217_ == 0 {
                    return v_bs_1216_;
                } else {
                    v_v_1218_ = lean_array_uget(v_bs_1216_, v_i_1215_);
                    v___x_1219_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1220_ = lean_array_uset(v_bs_1216_, v_i_1215_, v___x_1219_);
                    v___x_1221_ = l_instToJsonMessageActionItem_toJson(v_v_1218_);
                    v___x_1222_ = 1usize;
                    v___x_1223_ = lean_usize_add(v_i_1215_, v___x_1222_);
                    v___x_1224_ = lean_array_uset(v_bs_x27_1220_, v_i_1215_, v___x_1221_);
                    v_i_1215_ = v___x_1223_;
                    v_bs_1216_ = v___x_1224_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_1226_: *mut crate::leanh::LeanObject,
    mut v_i_1227_: *mut crate::leanh::LeanObject,
    mut v_bs_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1229_: usize = 0;
    let mut v_i_boxed_1230_: usize = 0;
    let mut v_res_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1229_ = crate::leanh::lean_unbox_usize(v_sz_1226_);
    crate::leanh::lean_dec(v_sz_1226_);
    v_i_boxed_1230_ = crate::leanh::lean_unbox_usize(v_i_1227_);
    crate::leanh::lean_dec(v_i_1227_);
    v_res_1231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_boxed_1229_, v_i_boxed_1230_, v_bs_1228_);
    return v_res_1231_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(
    mut v_a_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1233_: usize = 0;
    let mut v___x_1234_: usize = 0;
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1233_ = lean_array_size(v_a_1232_);
    v___x_1234_ = 0usize;
    v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_1233_, v___x_1234_, v_a_1232_);
    v___x_1236_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    return v___x_1236_;
}
pub unsafe fn l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(
    mut v_k_1237_: *mut crate::leanh::LeanObject,
    mut v_x_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1238_) == 0 {
        let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_1237_);
        v___x_1239_ = crate::leanh::lean_box(0);
        return v___x_1239_;
    } else {
        let mut v_val_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1240_ = crate::leanh::lean_ctor_get(v_x_1238_, 0);
        crate::leanh::lean_inc(v_val_1240_);
        crate::leanh::lean_dec_ref_known(v_x_1238_, 1);
        v___x_1241_ = l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(v_val_1240_);
        v___x_1242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1242_, 0, v_k_1237_);
        crate::leanh::lean_ctor_set(v___x_1242_, 1, v___x_1241_);
        v___x_1243_ = crate::leanh::lean_box(0);
        v___x_1244_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1244_, 0, v___x_1242_);
        crate::leanh::lean_ctor_set(v___x_1244_, 1, v___x_1243_);
        return v___x_1244_;
    }
}
pub unsafe fn l_instToJsonShowMessageRequestParams_toJson(
    mut v_x_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_1246_: u8 = 0;
    let mut v_message_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_actions_x3f_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_1246_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_1245_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_message_1247_ = crate::leanh::lean_ctor_get(v_x_1245_, 0);
                crate::leanh::lean_inc_ref(v_message_1247_);
                v_actions_x3f_1248_ = crate::leanh::lean_ctor_get(v_x_1245_, 1);
                crate::leanh::lean_inc(v_actions_x3f_1248_);
                crate::leanh::lean_dec_ref(v_x_1245_);
                v___x_1249_ = l_instFromJsonShowMessageParams_fromJson___closed__0;
                match v_type_1246_ {
                    0 => {
                        v___x_1267_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__1_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__1,
                        );
                        v___y_1251_ = v___x_1267_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1268_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__3),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__3_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__3,
                        );
                        v___y_1251_ = v___x_1268_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_1269_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__5),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__5_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__5,
                        );
                        v___y_1251_ = v___x_1269_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1270_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instToJsonMessageType___lam__0___closed__7),
                            core::ptr::addr_of_mut!(
                                l_instToJsonMessageType___lam__0___closed__7_once
                            ),
                            _init_l_instToJsonMessageType___lam__0___closed__7,
                        );
                        v___y_1251_ = v___x_1270_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1251_);
                v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1249_);
                crate::leanh::lean_ctor_set(v___x_1252_, 1, v___y_1251_);
                v___x_1253_ = crate::leanh::lean_box(0);
                v___x_1254_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1254_, 0, v___x_1252_);
                crate::leanh::lean_ctor_set(v___x_1254_, 1, v___x_1253_);
                v___x_1255_ = l_instFromJsonShowMessageParams_fromJson___closed__11;
                v___x_1256_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1256_, 0, v_message_1247_);
                v___x_1257_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1257_, 0, v___x_1255_);
                crate::leanh::lean_ctor_set(v___x_1257_, 1, v___x_1256_);
                v___x_1258_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
                crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1253_);
                v___x_1259_ = l_instFromJsonShowMessageRequestParams_fromJson___closed__8;
                v___x_1260_ =
                    l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(
                        v___x_1259_,
                        v_actions_x3f_1248_,
                    );
                v___x_1261_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1261_, 0, v___x_1260_);
                crate::leanh::lean_ctor_set(v___x_1261_, 1, v___x_1253_);
                v___x_1262_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1258_);
                crate::leanh::lean_ctor_set(v___x_1262_, 1, v___x_1261_);
                v___x_1263_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1263_, 0, v___x_1254_);
                crate::leanh::lean_ctor_set(v___x_1263_, 1, v___x_1262_);
                v___x_1264_ = l_instToJsonShowMessageParams_toJson___closed__0;
                v___x_1265_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(v___x_1263_, v___x_1264_);
                v___x_1266_ = l_Lean_Json_mkObj(v___x_1265_);
                crate::leanh::lean_dec(v___x_1265_);
                return v___x_1266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instFromJsonShowMessageResponse___aux__1(
    mut v_a_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = l_instFromJsonMessageActionItem___closed__0;
    v___x_1275_ = l_Option_fromJson_x3f___redArg(v___x_1274_, v_a_1273_);
    return v___x_1275_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00instFromJsonShowMessageResponse_spec__0(
    mut v_x_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1284_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut v_a_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1278_) == 0 {
                    v___x_1279_ = l_Option_fromJson_x3f___at___00instFromJsonShowMessageResponse_spec__0___closed__0;
                    return v___x_1279_;
                } else {
                    v___x_1280_ = l_instFromJsonMessageActionItem_fromJson(v_x_1278_);
                    if crate::leanh::lean_obj_tag(v___x_1280_) == 0 {
                        v_a_1281_ = crate::leanh::lean_ctor_get(v___x_1280_, 0);
                        v_isSharedCheck_1288_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1280_)) as u8;
                        if v_isSharedCheck_1288_ == 0 {
                            v___x_1283_ = v___x_1280_;
                            v_isShared_1284_ = v_isSharedCheck_1288_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1281_);
                            crate::leanh::lean_dec(v___x_1280_);
                            v___x_1283_ = crate::leanh::lean_box(0);
                            v_isShared_1284_ = v_isSharedCheck_1288_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1289_ = crate::leanh::lean_ctor_get(v___x_1280_, 0);
                        v_isSharedCheck_1297_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1280_)) as u8;
                        if v_isSharedCheck_1297_ == 0 {
                            v___x_1291_ = v___x_1280_;
                            v_isShared_1292_ = v_isSharedCheck_1297_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1289_);
                            crate::leanh::lean_dec(v___x_1280_);
                            v___x_1291_ = crate::leanh::lean_box(0);
                            v_isShared_1292_ = v_isSharedCheck_1297_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1284_ == 0 {
                    v___x_1286_ = v___x_1283_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
                    v___x_1286_ = v_reuseFailAlloc_1287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1286_;
            }
            3 => {
                v___x_1293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1293_, 0, v_a_1289_);
                if v_isShared_1292_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1291_, 0, v___x_1293_);
                    v___x_1295_ = v___x_1291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instToJsonShowMessageResponse___aux__1(
    mut v_a_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1301_ = l_instToJsonMessageActionItem___closed__0;
    v___x_1302_ = l_Option_toJson___redArg(v___x_1301_, v_a_1300_);
    return v___x_1302_;
}
pub unsafe fn l_Option_toJson___at___00instToJsonShowMessageResponse_spec__0(
    mut v_x_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1303_) == 0 {
        let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1304_ = crate::leanh::lean_box(0);
        return v___x_1304_;
    } else {
        let mut v_val_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1305_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
        crate::leanh::lean_inc(v_val_1305_);
        crate::leanh::lean_dec_ref_known(v_x_1303_, 1);
        v___x_1306_ = l_instToJsonMessageActionItem_toJson(v_val_1305_);
        return v___x_1306_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Window(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Window(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Window(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Window(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Window(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Window(builtin);
}
