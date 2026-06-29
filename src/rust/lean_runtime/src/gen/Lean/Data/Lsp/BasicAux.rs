// Lean compiler output
// Module: Lean.Data.Lsp.BasicAux
// Imports: Lean.Data.Json.FromToJson.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_nat_dec_eq, lean_nat_dec_lt, lean_uint64_mix_hash,
};
pub static l_Lean_Lsp_instInhabitedPosition_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instInhabitedPosition_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPosition_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedPosition_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPosition_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPosition_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instBEqPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqPosition_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instOrdPosition_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instOrdPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instHashablePosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instHashablePosition_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instHashablePosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instHashablePosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instHashablePosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instHashablePosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [108, 105, 110, 101, 0],
};
static mut l_Lean_Lsp_instToJsonPosition_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [99, 104, 97, 114, 97, 99, 116, 101, 114, 0],
};
static mut l_Lean_Lsp_instToJsonPosition_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPosition_toJson___closed__2_value: crate::leanh::LeanArrayObject<
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
static mut l_Lean_Lsp_instToJsonPosition_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonPosition_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value:
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
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value:
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
    m_data: [80, 111, 115, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13828015092876872733 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7347781233040561197 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10_value:
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
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10457452386710778163 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonPosition_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__2_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__3_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__7_value:
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
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition_repr___redArg___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprPosition_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instReprPosition_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instReprPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instReprPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToStringPosition___lam__0___closed__0_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Lsp_instToStringPosition___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringPosition___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToStringPosition___lam__0___closed__1_value:
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
    m_data: [44, 32, 0],
};
static mut l_Lean_Lsp_instToStringPosition___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringPosition___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToStringPosition___lam__0___closed__2_value:
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
    m_data: [41, 0],
};
static mut l_Lean_Lsp_instToStringPosition___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringPosition___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToStringPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToStringPosition___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToStringPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToStringPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instLTPosition: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instLEPosition: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instInhabitedRange_default___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPosition_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPosition_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instInhabitedRange_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedRange_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedRange_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedRange_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedRange_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instBEqRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqRange_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqRange___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqRange___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instHashableRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instHashableRange_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instHashableRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instHashableRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instHashableRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instHashableRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRange_toJson___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [115, 116, 97, 114, 116, 0],
    };
static mut l_Lean_Lsp_instToJsonRange_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRange_toJson___closed__1_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [101, 110, 100, 0],
    };
static mut l_Lean_Lsp_instToJsonRange_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRange_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonRange_fromJson___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [82, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14633677404122224040 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRange_fromJson___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12748178501718933929 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRange_fromJson___closed__8_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7094185473178890951 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRange_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRange_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instOrdRange_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instOrdRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdRange___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdRange___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprRange_repr___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprRange_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprRange_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instReprRange_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprRange_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instReprRange_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instReprRange_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprRange_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprRange_repr___redArg___closed__4_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonRange_toJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprRange_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprRange_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instReprRange_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instReprRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instReprRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instLTRange: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instLERange: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Lsp_instBEqPosition_beq(
    mut v_x_514_: *mut crate::leanh::LeanObject,
    mut v_x_515_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_line_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u8 = 0;
    v_line_516_ = crate::leanh::lean_ctor_get(v_x_514_, 0);
    v_character_517_ = crate::leanh::lean_ctor_get(v_x_514_, 1);
    v_line_518_ = crate::leanh::lean_ctor_get(v_x_515_, 0);
    v_character_519_ = crate::leanh::lean_ctor_get(v_x_515_, 1);
    v___x_520_ = lean_nat_dec_eq(v_line_516_, v_line_518_);
    if v___x_520_ == 0 {
        return v___x_520_;
    } else {
        let mut v___x_521_: u8 = 0;
        v___x_521_ = lean_nat_dec_eq(v_character_517_, v_character_519_);
        return v___x_521_;
    }
}
pub unsafe fn l_Lean_Lsp_instBEqPosition_beq___boxed(
    mut v_x_522_: *mut crate::leanh::LeanObject,
    mut v_x_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_524_: u8 = 0;
    let mut v_r_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lean_Lsp_instBEqPosition_beq(v_x_522_, v_x_523_);
    crate::leanh::lean_dec_ref(v_x_523_);
    crate::leanh::lean_dec_ref(v_x_522_);
    v_r_525_ = crate::leanh::lean_box((v_res_524_) as usize);
    return v_r_525_;
}
pub unsafe fn l_Lean_Lsp_instOrdPosition_ord(
    mut v_x_528_: *mut crate::leanh::LeanObject,
    mut v_x_529_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_line_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    v_line_530_ = crate::leanh::lean_ctor_get(v_x_528_, 0);
    v_character_531_ = crate::leanh::lean_ctor_get(v_x_528_, 1);
    v_line_532_ = crate::leanh::lean_ctor_get(v_x_529_, 0);
    v_character_533_ = crate::leanh::lean_ctor_get(v_x_529_, 1);
    v___x_534_ = lean_nat_dec_lt(v_line_530_, v_line_532_);
    if v___x_534_ == 0 {
        let mut v___x_535_: u8 = 0;
        v___x_535_ = lean_nat_dec_eq(v_line_530_, v_line_532_);
        if v___x_535_ == 0 {
            let mut v___x_536_: u8 = 0;
            v___x_536_ = 2;
            return v___x_536_;
        } else {
            let mut v___x_537_: u8 = 0;
            v___x_537_ = lean_nat_dec_lt(v_character_531_, v_character_533_);
            if v___x_537_ == 0 {
                let mut v___x_538_: u8 = 0;
                v___x_538_ = lean_nat_dec_eq(v_character_531_, v_character_533_);
                if v___x_538_ == 0 {
                    let mut v___x_539_: u8 = 0;
                    v___x_539_ = 2;
                    return v___x_539_;
                } else {
                    let mut v___x_540_: u8 = 0;
                    v___x_540_ = 1;
                    return v___x_540_;
                }
            } else {
                let mut v___x_541_: u8 = 0;
                v___x_541_ = 0;
                return v___x_541_;
            }
        }
    } else {
        let mut v___x_542_: u8 = 0;
        v___x_542_ = 0;
        return v___x_542_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdPosition_ord___boxed(
    mut v_x_543_: *mut crate::leanh::LeanObject,
    mut v_x_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_545_: u8 = 0;
    let mut v_r_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_Lsp_instOrdPosition_ord(v_x_543_, v_x_544_);
    crate::leanh::lean_dec_ref(v_x_544_);
    crate::leanh::lean_dec_ref(v_x_543_);
    v_r_546_ = crate::leanh::lean_box((v_res_545_) as usize);
    return v_r_546_;
}
pub unsafe fn l_Lean_Lsp_instHashablePosition_hash(
    mut v_x_549_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_line_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: u64 = 0;
    let mut v___x_553_: u64 = 0;
    let mut v___x_554_: u64 = 0;
    let mut v___x_555_: u64 = 0;
    let mut v___x_556_: u64 = 0;
    v_line_550_ = crate::leanh::lean_ctor_get(v_x_549_, 0);
    v_character_551_ = crate::leanh::lean_ctor_get(v_x_549_, 1);
    v___x_552_ = 0u64;
    v___x_553_ = lean_uint64_of_nat(v_line_550_);
    v___x_554_ = lean_uint64_mix_hash(v___x_552_, v___x_553_);
    v___x_555_ = lean_uint64_of_nat(v_character_551_);
    v___x_556_ = lean_uint64_mix_hash(v___x_554_, v___x_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_Lsp_instHashablePosition_hash___boxed(
    mut v_x_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: u64 = 0;
    let mut v_r_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Lean_Lsp_instHashablePosition_hash(v_x_557_);
    crate::leanh::lean_dec_ref(v_x_557_);
    v_r_559_ = crate::leanh::lean_box_uint64(v_res_558_);
    return v_r_559_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_562_) == 0 {
                    v___x_564_ = lean_array_to_list(v_a_563_);
                    return v___x_564_;
                } else {
                    v_head_565_ = crate::leanh::lean_ctor_get(v_a_562_, 0);
                    crate::leanh::lean_inc(v_head_565_);
                    v_tail_566_ = crate::leanh::lean_ctor_get(v_a_562_, 1);
                    crate::leanh::lean_inc(v_tail_566_);
                    crate::leanh::lean_dec_ref_known(v_a_562_, 2);
                    v___x_567_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_563_,
                        v_head_565_,
                    );
                    v_a_562_ = v_tail_566_;
                    v_a_563_ = v___x_567_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonPosition_toJson(
    mut v_x_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_578_: u8 = 0;
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_574_ = crate::leanh::lean_ctor_get(v_x_573_, 0);
                v_character_575_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
                v_isSharedCheck_597_ = (!crate::leanh::lean_is_exclusive(v_x_573_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_577_ = v_x_573_;
                    v_isShared_578_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_character_575_);
                    crate::leanh::lean_inc(v_line_574_);
                    crate::leanh::lean_dec(v_x_573_);
                    v___x_577_ = crate::leanh::lean_box(0);
                    v_isShared_578_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_579_ = l_Lean_Lsp_instToJsonPosition_toJson___closed__0;
                v___x_580_ = l_Lean_JsonNumber_fromNat(v_line_574_);
                v___x_581_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_581_, 0, v___x_580_);
                if v_isShared_578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_577_, 1, v___x_581_);
                    crate::leanh::lean_ctor_set(v___x_577_, 0, v___x_579_);
                    v___x_583_ = v___x_577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_581_);
                    v___x_583_ = v_reuseFailAlloc_596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_584_ = crate::leanh::lean_box(0);
                v___x_585_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_585_, 0, v___x_583_);
                crate::leanh::lean_ctor_set(v___x_585_, 1, v___x_584_);
                v___x_586_ = l_Lean_Lsp_instToJsonPosition_toJson___closed__1;
                v___x_587_ = l_Lean_JsonNumber_fromNat(v_character_575_);
                v___x_588_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_588_, 0, v___x_587_);
                v___x_589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_589_, 0, v___x_586_);
                crate::leanh::lean_ctor_set(v___x_589_, 1, v___x_588_);
                v___x_590_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_590_, 0, v___x_589_);
                crate::leanh::lean_ctor_set(v___x_590_, 1, v___x_584_);
                v___x_591_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_591_, 0, v___x_590_);
                crate::leanh::lean_ctor_set(v___x_591_, 1, v___x_584_);
                v___x_592_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_585_);
                crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_591_);
                v___x_593_ = l_Lean_Lsp_instToJsonPosition_toJson___closed__2;
                v___x_594_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_592_, v___x_593_);
                v___x_595_ = l_Lean_Json_mkObj(v___x_594_);
                crate::leanh::lean_dec(v___x_594_);
                return v___x_595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(
    mut v_j_600_: *mut crate::leanh::LeanObject,
    mut v_k_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = l_Lean_Json_getObjValD(v_j_600_, v_k_601_);
    v___x_603_ = l_Lean_Json_getNat_x3f(v___x_602_);
    return v___x_603_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0___boxed(
    mut v_j_604_: *mut crate::leanh::LeanObject,
    mut v_k_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(
            v_j_604_, v_k_605_,
        );
    crate::leanh::lean_dec_ref(v_k_605_);
    return v_res_606_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = 1;
    v___x_615_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3;
    v___x_616_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_615_, v___x_614_);
    return v___x_616_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5;
    v___x_619_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4,
    );
    v___x_620_ = lean_string_append(v___x_619_, v___x_618_);
    return v___x_620_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_623_: u8 = 0;
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_623_ = 1;
    v___x_624_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7;
    v___x_625_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_624_, v___x_623_);
    return v___x_625_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_626_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8,
    );
    v___x_627_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6,
    );
    v___x_628_ = lean_string_append(v___x_627_, v___x_626_);
    return v___x_628_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10;
    v___x_631_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9,
    );
    v___x_632_ = lean_string_append(v___x_631_, v___x_630_);
    return v___x_632_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ = 1;
    v___x_636_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12;
    v___x_637_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_636_, v___x_635_);
    return v___x_637_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13,
    );
    v___x_639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6,
    );
    v___x_640_ = lean_string_append(v___x_639_, v___x_638_);
    return v___x_640_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_641_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10;
    v___x_642_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14,
    );
    v___x_643_ = lean_string_append(v___x_642_, v___x_641_);
    return v___x_643_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonPosition_fromJson(
    mut v_json_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_650_: u8 = 0;
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_a_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut v_a_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_671_: u8 = 0;
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_677_: u8 = 0;
    let mut v_a_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_681_: u8 = 0;
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_685_: u8 = 0;
    let mut v_a_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_645_ = l_Lean_Lsp_instToJsonPosition_toJson___closed__0;
                crate::leanh::lean_inc(v_json_644_);
                v___x_646_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_644_, v___x_645_);
                if crate::leanh::lean_obj_tag(v___x_646_) == 0 {
                    crate::leanh::lean_dec(v_json_644_);
                    v_a_647_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
                    v_isSharedCheck_656_ = (!crate::leanh::lean_is_exclusive(v___x_646_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_649_ = v___x_646_;
                        v_isShared_650_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_647_);
                        crate::leanh::lean_dec(v___x_646_);
                        v___x_649_ = crate::leanh::lean_box(0);
                        v_isShared_650_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_646_) == 0 {
                        crate::leanh::lean_dec(v_json_644_);
                        v_a_657_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
                        v_isSharedCheck_664_ = (!crate::leanh::lean_is_exclusive(v___x_646_)) as u8;
                        if v_isSharedCheck_664_ == 0 {
                            v___x_659_ = v___x_646_;
                            v_isShared_660_ = v_isSharedCheck_664_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_657_);
                            crate::leanh::lean_dec(v___x_646_);
                            v___x_659_ = crate::leanh::lean_box(0);
                            v_isShared_660_ = v_isSharedCheck_664_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_665_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
                        crate::leanh::lean_inc(v_a_665_);
                        crate::leanh::lean_dec_ref_known(v___x_646_, 1);
                        v___x_666_ = l_Lean_Lsp_instToJsonPosition_toJson___closed__1;
                        v___x_667_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_644_, v___x_666_);
                        if crate::leanh::lean_obj_tag(v___x_667_) == 0 {
                            crate::leanh::lean_dec(v_a_665_);
                            v_a_668_ = crate::leanh::lean_ctor_get(v___x_667_, 0);
                            v_isSharedCheck_677_ =
                                (!crate::leanh::lean_is_exclusive(v___x_667_)) as u8;
                            if v_isSharedCheck_677_ == 0 {
                                v___x_670_ = v___x_667_;
                                v_isShared_671_ = v_isSharedCheck_677_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_668_);
                                crate::leanh::lean_dec(v___x_667_);
                                v___x_670_ = crate::leanh::lean_box(0);
                                v_isShared_671_ = v_isSharedCheck_677_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_667_) == 0 {
                                crate::leanh::lean_dec(v_a_665_);
                                v_a_678_ = crate::leanh::lean_ctor_get(v___x_667_, 0);
                                v_isSharedCheck_685_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_667_)) as u8;
                                if v_isSharedCheck_685_ == 0 {
                                    v___x_680_ = v___x_667_;
                                    v_isShared_681_ = v_isSharedCheck_685_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_678_);
                                    crate::leanh::lean_dec(v___x_667_);
                                    v___x_680_ = crate::leanh::lean_box(0);
                                    v_isShared_681_ = v_isSharedCheck_685_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_686_ = crate::leanh::lean_ctor_get(v___x_667_, 0);
                                v_isSharedCheck_694_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_667_)) as u8;
                                if v_isSharedCheck_694_ == 0 {
                                    v___x_688_ = v___x_667_;
                                    v_isShared_689_ = v_isSharedCheck_694_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_686_);
                                    crate::leanh::lean_dec(v___x_667_);
                                    v___x_688_ = crate::leanh::lean_box(0);
                                    v_isShared_689_ = v_isSharedCheck_694_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_651_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11,
                );
                v___x_652_ = lean_string_append(v___x_651_, v_a_647_);
                crate::leanh::lean_dec(v_a_647_);
                if v_isShared_650_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_652_);
                    v___x_654_ = v___x_649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_654_;
            }
            3 => {
                if v_isShared_660_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_659_, 0);
                    v___x_662_ = v___x_659_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
                    v___x_662_ = v_reuseFailAlloc_663_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_662_;
            }
            5 => {
                v___x_672_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15,
                );
                v___x_673_ = lean_string_append(v___x_672_, v_a_668_);
                crate::leanh::lean_dec(v_a_668_);
                if v_isShared_671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_673_);
                    v___x_675_ = v___x_670_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
                    v___x_675_ = v_reuseFailAlloc_676_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_675_;
            }
            7 => {
                if v_isShared_681_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_680_, 0);
                    v___x_683_ = v___x_680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
                    v___x_683_ = v_reuseFailAlloc_684_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_683_;
            }
            9 => {
                v___x_690_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_690_, 0, v_a_665_);
                crate::leanh::lean_ctor_set(v___x_690_, 1, v_a_686_);
                if v_isShared_689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_688_, 0, v___x_690_);
                    v___x_692_ = v___x_688_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
                    v___x_692_ = v_reuseFailAlloc_693_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Lsp_instReprPosition_repr_spec__0(
    mut v_a_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = lean_nat_to_int(v_a_697_);
    return v___x_698_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_712_ = lean_nat_to_int(v___x_711_);
    return v___x_712_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_719_ = lean_nat_to_int(v___x_718_);
    return v___x_719_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__0;
    v___x_722_ = lean_string_length(v___x_721_);
    return v___x_722_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_723_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once),
        _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12,
    );
    v___x_724_ = lean_nat_to_int(v___x_723_);
    return v___x_724_;
}
pub unsafe fn l_Lean_Lsp_instReprPosition_repr___redArg(
    mut v_x_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_734_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_730_ = crate::leanh::lean_ctor_get(v_x_729_, 0);
                v_character_731_ = crate::leanh::lean_ctor_get(v_x_729_, 1);
                v_isSharedCheck_766_ = (!crate::leanh::lean_is_exclusive(v_x_729_)) as u8;
                if v_isSharedCheck_766_ == 0 {
                    v___x_733_ = v_x_729_;
                    v_isShared_734_ = v_isSharedCheck_766_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_character_731_);
                    crate::leanh::lean_inc(v_line_730_);
                    crate::leanh::lean_dec(v_x_729_);
                    v___x_733_ = crate::leanh::lean_box(0);
                    v_isShared_734_ = v_isSharedCheck_766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_735_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__4;
                v___x_736_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__5;
                v___x_737_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once
                    ),
                    _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6,
                );
                v___x_738_ = l_Nat_reprFast(v_line_730_);
                v___x_739_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_739_, 0, v___x_738_);
                if v_isShared_734_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_733_, 4);
                    crate::leanh::lean_ctor_set(v___x_733_, 1, v___x_739_);
                    crate::leanh::lean_ctor_set(v___x_733_, 0, v___x_737_);
                    v___x_741_ = v___x_733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_739_);
                    v___x_741_ = v_reuseFailAlloc_765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_742_ = 0;
                v___x_743_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_743_, 0, v___x_741_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_743_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_742_,
                );
                v___x_744_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_744_, 0, v___x_736_);
                crate::leanh::lean_ctor_set(v___x_744_, 1, v___x_743_);
                v___x_745_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__8;
                v___x_746_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_746_, 0, v___x_744_);
                crate::leanh::lean_ctor_set(v___x_746_, 1, v___x_745_);
                v___x_747_ = crate::leanh::lean_box(1);
                v___x_748_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_748_, 0, v___x_746_);
                crate::leanh::lean_ctor_set(v___x_748_, 1, v___x_747_);
                v___x_749_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__9;
                v___x_750_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_750_, 0, v___x_748_);
                crate::leanh::lean_ctor_set(v___x_750_, 1, v___x_749_);
                v___x_751_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_751_, 0, v___x_750_);
                crate::leanh::lean_ctor_set(v___x_751_, 1, v___x_735_);
                v___x_752_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__10),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10,
                );
                v___x_753_ = l_Nat_reprFast(v_character_731_);
                v___x_754_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_754_, 0, v___x_753_);
                v___x_755_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_755_, 0, v___x_752_);
                crate::leanh::lean_ctor_set(v___x_755_, 1, v___x_754_);
                v___x_756_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_756_, 0, v___x_755_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_756_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_742_,
                );
                v___x_757_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_751_);
                crate::leanh::lean_ctor_set(v___x_757_, 1, v___x_756_);
                v___x_758_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13,
                );
                v___x_759_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__14;
                v___x_760_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_760_, 0, v___x_759_);
                crate::leanh::lean_ctor_set(v___x_760_, 1, v___x_757_);
                v___x_761_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__15;
                v___x_762_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_762_, 0, v___x_760_);
                crate::leanh::lean_ctor_set(v___x_762_, 1, v___x_761_);
                v___x_763_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_763_, 0, v___x_758_);
                crate::leanh::lean_ctor_set(v___x_763_, 1, v___x_762_);
                v___x_764_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_764_, 0, v___x_763_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_764_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_742_,
                );
                return v___x_764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instReprPosition_repr(
    mut v_x_767_: *mut crate::leanh::LeanObject,
    mut v_prec_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_769_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_x_767_);
    return v___x_769_;
}
pub unsafe fn l_Lean_Lsp_instReprPosition_repr___boxed(
    mut v_x_770_: *mut crate::leanh::LeanObject,
    mut v_prec_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Lean_Lsp_instReprPosition_repr(v_x_770_, v_prec_771_);
    crate::leanh::lean_dec(v_prec_771_);
    return v_res_772_;
}
pub unsafe fn l_Lean_Lsp_instToStringPosition___lam__0(
    mut v_p_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_line_779_ = crate::leanh::lean_ctor_get(v_p_778_, 0);
    crate::leanh::lean_inc(v_line_779_);
    v_character_780_ = crate::leanh::lean_ctor_get(v_p_778_, 1);
    crate::leanh::lean_inc(v_character_780_);
    crate::leanh::lean_dec_ref(v_p_778_);
    v___x_781_ = l_Lean_Lsp_instToStringPosition___lam__0___closed__0;
    v___x_782_ = l_Nat_reprFast(v_line_779_);
    v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
    crate::leanh::lean_dec_ref(v___x_782_);
    v___x_784_ = l_Lean_Lsp_instToStringPosition___lam__0___closed__1;
    v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
    v___x_786_ = l_Nat_reprFast(v_character_780_);
    v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
    crate::leanh::lean_dec_ref(v___x_786_);
    v___x_788_ = l_Lean_Lsp_instToStringPosition___lam__0___closed__2;
    v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
    return v___x_789_;
}
pub unsafe fn _init_l_Lean_Lsp_instLTPosition() -> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = crate::leanh::lean_box(0);
    return v___x_792_;
}
pub unsafe fn _init_l_Lean_Lsp_instLEPosition() -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = crate::leanh::lean_box(0);
    return v___x_793_;
}
pub unsafe fn l_Lean_Lsp_instBEqRange_beq(
    mut v_x_798_: *mut crate::leanh::LeanObject,
    mut v_x_799_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_start_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: u8 = 0;
    v_start_800_ = crate::leanh::lean_ctor_get(v_x_798_, 0);
    v_end_801_ = crate::leanh::lean_ctor_get(v_x_798_, 1);
    v_start_802_ = crate::leanh::lean_ctor_get(v_x_799_, 0);
    v_end_803_ = crate::leanh::lean_ctor_get(v_x_799_, 1);
    v___x_804_ = l_Lean_Lsp_instBEqPosition_beq(v_start_800_, v_start_802_);
    if v___x_804_ == 0 {
        return v___x_804_;
    } else {
        let mut v___x_805_: u8 = 0;
        v___x_805_ = l_Lean_Lsp_instBEqPosition_beq(v_end_801_, v_end_803_);
        return v___x_805_;
    }
}
pub unsafe fn l_Lean_Lsp_instBEqRange_beq___boxed(
    mut v_x_806_: *mut crate::leanh::LeanObject,
    mut v_x_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_808_: u8 = 0;
    let mut v_r_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_Lsp_instBEqRange_beq(v_x_806_, v_x_807_);
    crate::leanh::lean_dec_ref(v_x_807_);
    crate::leanh::lean_dec_ref(v_x_806_);
    v_r_809_ = crate::leanh::lean_box((v_res_808_) as usize);
    return v_r_809_;
}
pub unsafe fn l_Lean_Lsp_instHashableRange_hash(
    mut v_x_812_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_start_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: u64 = 0;
    let mut v___x_816_: u64 = 0;
    let mut v___x_817_: u64 = 0;
    let mut v___x_818_: u64 = 0;
    let mut v___x_819_: u64 = 0;
    v_start_813_ = crate::leanh::lean_ctor_get(v_x_812_, 0);
    v_end_814_ = crate::leanh::lean_ctor_get(v_x_812_, 1);
    v___x_815_ = 0u64;
    v___x_816_ = l_Lean_Lsp_instHashablePosition_hash(v_start_813_);
    v___x_817_ = lean_uint64_mix_hash(v___x_815_, v___x_816_);
    v___x_818_ = l_Lean_Lsp_instHashablePosition_hash(v_end_814_);
    v___x_819_ = lean_uint64_mix_hash(v___x_817_, v___x_818_);
    return v___x_819_;
}
pub unsafe fn l_Lean_Lsp_instHashableRange_hash___boxed(
    mut v_x_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_821_: u64 = 0;
    let mut v_r_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_821_ = l_Lean_Lsp_instHashableRange_hash(v_x_820_);
    crate::leanh::lean_dec_ref(v_x_820_);
    v_r_822_ = crate::leanh::lean_box_uint64(v_res_821_);
    return v_r_822_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRange_toJson(
    mut v_x_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_832_: u8 = 0;
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_828_ = crate::leanh::lean_ctor_get(v_x_827_, 0);
                v_end_829_ = crate::leanh::lean_ctor_get(v_x_827_, 1);
                v_isSharedCheck_849_ = (!crate::leanh::lean_is_exclusive(v_x_827_)) as u8;
                if v_isSharedCheck_849_ == 0 {
                    v___x_831_ = v_x_827_;
                    v_isShared_832_ = v_isSharedCheck_849_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_end_829_);
                    crate::leanh::lean_inc(v_start_828_);
                    crate::leanh::lean_dec(v_x_827_);
                    v___x_831_ = crate::leanh::lean_box(0);
                    v_isShared_832_ = v_isSharedCheck_849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_833_ = l_Lean_Lsp_instToJsonRange_toJson___closed__0;
                v___x_834_ = l_Lean_Lsp_instToJsonPosition_toJson(v_start_828_);
                if v_isShared_832_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_831_, 1, v___x_834_);
                    crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_833_);
                    v___x_836_ = v___x_831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_834_);
                    v___x_836_ = v_reuseFailAlloc_848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_837_ = crate::leanh::lean_box(0);
                v___x_838_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_838_, 0, v___x_836_);
                crate::leanh::lean_ctor_set(v___x_838_, 1, v___x_837_);
                v___x_839_ = l_Lean_Lsp_instToJsonRange_toJson___closed__1;
                v___x_840_ = l_Lean_Lsp_instToJsonPosition_toJson(v_end_829_);
                v___x_841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_841_, 0, v___x_839_);
                crate::leanh::lean_ctor_set(v___x_841_, 1, v___x_840_);
                v___x_842_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_842_, 0, v___x_841_);
                crate::leanh::lean_ctor_set(v___x_842_, 1, v___x_837_);
                v___x_843_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_843_, 0, v___x_842_);
                crate::leanh::lean_ctor_set(v___x_843_, 1, v___x_837_);
                v___x_844_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_844_, 0, v___x_838_);
                crate::leanh::lean_ctor_set(v___x_844_, 1, v___x_843_);
                v___x_845_ = l_Lean_Lsp_instToJsonPosition_toJson___closed__2;
                v___x_846_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_844_, v___x_845_);
                v___x_847_ = l_Lean_Json_mkObj(v___x_846_);
                crate::leanh::lean_dec(v___x_846_);
                return v___x_847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(
    mut v_j_852_: *mut crate::leanh::LeanObject,
    mut v_k_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l_Lean_Json_getObjValD(v_j_852_, v_k_853_);
    v___x_855_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0___boxed(
    mut v_j_856_: *mut crate::leanh::LeanObject,
    mut v_k_857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_858_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(
        v_j_856_, v_k_857_,
    );
    crate::leanh::lean_dec_ref(v_k_857_);
    return v_res_858_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = 1;
    v___x_865_ = l_Lean_Lsp_instFromJsonRange_fromJson___closed__1;
    v___x_866_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_865_, v___x_864_);
    return v___x_866_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5;
    v___x_868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2,
    );
    v___x_869_ = lean_string_append(v___x_868_, v___x_867_);
    return v___x_869_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = 1;
    v___x_873_ = l_Lean_Lsp_instFromJsonRange_fromJson___closed__4;
    v___x_874_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5,
    );
    v___x_876_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3,
    );
    v___x_877_ = lean_string_append(v___x_876_, v___x_875_);
    return v___x_877_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10;
    v___x_879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6,
    );
    v___x_880_ = lean_string_append(v___x_879_, v___x_878_);
    return v___x_880_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_883_: u8 = 0;
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ = 1;
    v___x_884_ = l_Lean_Lsp_instFromJsonRange_fromJson___closed__8;
    v___x_885_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_884_, v___x_883_);
    return v___x_885_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9,
    );
    v___x_887_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3,
    );
    v___x_888_ = lean_string_append(v___x_887_, v___x_886_);
    return v___x_888_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10;
    v___x_890_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once),
        _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10,
    );
    v___x_891_ = lean_string_append(v___x_890_, v___x_889_);
    return v___x_891_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRange_fromJson(
    mut v_json_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_904_: u8 = 0;
    let mut v_a_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut v_a_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_925_: u8 = 0;
    let mut v_a_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v_a_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_893_ = l_Lean_Lsp_instToJsonRange_toJson___closed__0;
                crate::leanh::lean_inc(v_json_892_);
                v___x_894_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_892_, v___x_893_);
                if crate::leanh::lean_obj_tag(v___x_894_) == 0 {
                    crate::leanh::lean_dec(v_json_892_);
                    v_a_895_ = crate::leanh::lean_ctor_get(v___x_894_, 0);
                    v_isSharedCheck_904_ = (!crate::leanh::lean_is_exclusive(v___x_894_)) as u8;
                    if v_isSharedCheck_904_ == 0 {
                        v___x_897_ = v___x_894_;
                        v_isShared_898_ = v_isSharedCheck_904_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_895_);
                        crate::leanh::lean_dec(v___x_894_);
                        v___x_897_ = crate::leanh::lean_box(0);
                        v_isShared_898_ = v_isSharedCheck_904_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_894_) == 0 {
                        crate::leanh::lean_dec(v_json_892_);
                        v_a_905_ = crate::leanh::lean_ctor_get(v___x_894_, 0);
                        v_isSharedCheck_912_ = (!crate::leanh::lean_is_exclusive(v___x_894_)) as u8;
                        if v_isSharedCheck_912_ == 0 {
                            v___x_907_ = v___x_894_;
                            v_isShared_908_ = v_isSharedCheck_912_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_905_);
                            crate::leanh::lean_dec(v___x_894_);
                            v___x_907_ = crate::leanh::lean_box(0);
                            v_isShared_908_ = v_isSharedCheck_912_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_913_ = crate::leanh::lean_ctor_get(v___x_894_, 0);
                        crate::leanh::lean_inc(v_a_913_);
                        crate::leanh::lean_dec_ref_known(v___x_894_, 1);
                        v___x_914_ = l_Lean_Lsp_instToJsonRange_toJson___closed__1;
                        v___x_915_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_892_, v___x_914_);
                        if crate::leanh::lean_obj_tag(v___x_915_) == 0 {
                            crate::leanh::lean_dec(v_a_913_);
                            v_a_916_ = crate::leanh::lean_ctor_get(v___x_915_, 0);
                            v_isSharedCheck_925_ =
                                (!crate::leanh::lean_is_exclusive(v___x_915_)) as u8;
                            if v_isSharedCheck_925_ == 0 {
                                v___x_918_ = v___x_915_;
                                v_isShared_919_ = v_isSharedCheck_925_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_916_);
                                crate::leanh::lean_dec(v___x_915_);
                                v___x_918_ = crate::leanh::lean_box(0);
                                v_isShared_919_ = v_isSharedCheck_925_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_915_) == 0 {
                                crate::leanh::lean_dec(v_a_913_);
                                v_a_926_ = crate::leanh::lean_ctor_get(v___x_915_, 0);
                                v_isSharedCheck_933_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_915_)) as u8;
                                if v_isSharedCheck_933_ == 0 {
                                    v___x_928_ = v___x_915_;
                                    v_isShared_929_ = v_isSharedCheck_933_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_926_);
                                    crate::leanh::lean_dec(v___x_915_);
                                    v___x_928_ = crate::leanh::lean_box(0);
                                    v_isShared_929_ = v_isSharedCheck_933_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_934_ = crate::leanh::lean_ctor_get(v___x_915_, 0);
                                v_isSharedCheck_942_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_915_)) as u8;
                                if v_isSharedCheck_942_ == 0 {
                                    v___x_936_ = v___x_915_;
                                    v_isShared_937_ = v_isSharedCheck_942_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_934_);
                                    crate::leanh::lean_dec(v___x_915_);
                                    v___x_936_ = crate::leanh::lean_box(0);
                                    v_isShared_937_ = v_isSharedCheck_942_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_899_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once),
                    _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7,
                );
                v___x_900_ = lean_string_append(v___x_899_, v_a_895_);
                crate::leanh::lean_dec(v_a_895_);
                if v_isShared_898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_897_, 0, v___x_900_);
                    v___x_902_ = v___x_897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
                    v___x_902_ = v_reuseFailAlloc_903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_902_;
            }
            3 => {
                if v_isShared_908_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_907_, 0);
                    v___x_910_ = v___x_907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
                    v___x_910_ = v_reuseFailAlloc_911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_910_;
            }
            5 => {
                v___x_920_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRange_fromJson___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11,
                );
                v___x_921_ = lean_string_append(v___x_920_, v_a_916_);
                crate::leanh::lean_dec(v_a_916_);
                if v_isShared_919_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_921_);
                    v___x_923_ = v___x_918_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
                    v___x_923_ = v_reuseFailAlloc_924_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_923_;
            }
            7 => {
                if v_isShared_929_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_928_, 0);
                    v___x_931_ = v___x_928_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_931_;
            }
            9 => {
                v___x_938_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_938_, 0, v_a_913_);
                crate::leanh::lean_ctor_set(v___x_938_, 1, v_a_934_);
                if v_isShared_937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_938_);
                    v___x_940_ = v___x_936_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
                    v___x_940_ = v_reuseFailAlloc_941_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instOrdRange_ord(
    mut v_x_945_: *mut crate::leanh::LeanObject,
    mut v_x_946_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_start_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: u8 = 0;
    v_start_947_ = crate::leanh::lean_ctor_get(v_x_945_, 0);
    v_end_948_ = crate::leanh::lean_ctor_get(v_x_945_, 1);
    v_start_949_ = crate::leanh::lean_ctor_get(v_x_946_, 0);
    v_end_950_ = crate::leanh::lean_ctor_get(v_x_946_, 1);
    v___x_951_ = l_Lean_Lsp_instOrdPosition_ord(v_start_947_, v_start_949_);
    if v___x_951_ == 1 {
        let mut v___x_952_: u8 = 0;
        v___x_952_ = l_Lean_Lsp_instOrdPosition_ord(v_end_948_, v_end_950_);
        if v___x_952_ == 1 {
            return v___x_952_;
        } else {
            return v___x_952_;
        }
    } else {
        return v___x_951_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdRange_ord___boxed(
    mut v_x_953_: *mut crate::leanh::LeanObject,
    mut v_x_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_955_: u8 = 0;
    let mut v_r_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_Lsp_instOrdRange_ord(v_x_953_, v_x_954_);
    crate::leanh::lean_dec_ref(v_x_954_);
    crate::leanh::lean_dec_ref(v_x_953_);
    v_r_956_ = crate::leanh::lean_box((v_res_955_) as usize);
    return v_r_956_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_968_ = lean_nat_to_int(v___x_967_);
    return v___x_968_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_971_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_972_ = lean_nat_to_int(v___x_971_);
    return v___x_972_;
}
pub unsafe fn l_Lean_Lsp_instReprRange_repr___redArg(
    mut v_x_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_978_: u8 = 0;
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_974_ = crate::leanh::lean_ctor_get(v_x_973_, 0);
                v_end_975_ = crate::leanh::lean_ctor_get(v_x_973_, 1);
                v_isSharedCheck_1008_ = (!crate::leanh::lean_is_exclusive(v_x_973_)) as u8;
                if v_isSharedCheck_1008_ == 0 {
                    v___x_977_ = v_x_973_;
                    v_isShared_978_ = v_isSharedCheck_1008_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_end_975_);
                    crate::leanh::lean_inc(v_start_974_);
                    crate::leanh::lean_dec(v_x_973_);
                    v___x_977_ = crate::leanh::lean_box(0);
                    v_isShared_978_ = v_isSharedCheck_1008_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_979_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__4;
                v___x_980_ = l_Lean_Lsp_instReprRange_repr___redArg___closed__2;
                v___x_981_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprRange_repr___redArg___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once
                    ),
                    _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3,
                );
                v___x_982_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_start_974_);
                if v_isShared_978_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_977_, 4);
                    crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_982_);
                    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_981_);
                    v___x_984_ = v___x_977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 1, v___x_982_);
                    v___x_984_ = v_reuseFailAlloc_1007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_985_ = 0;
                v___x_986_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_985_,
                );
                v___x_987_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_980_);
                crate::leanh::lean_ctor_set(v___x_987_, 1, v___x_986_);
                v___x_988_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__8;
                v___x_989_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_987_);
                crate::leanh::lean_ctor_set(v___x_989_, 1, v___x_988_);
                v___x_990_ = crate::leanh::lean_box(1);
                v___x_991_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_989_);
                crate::leanh::lean_ctor_set(v___x_991_, 1, v___x_990_);
                v___x_992_ = l_Lean_Lsp_instReprRange_repr___redArg___closed__4;
                v___x_993_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_993_, 0, v___x_991_);
                crate::leanh::lean_ctor_set(v___x_993_, 1, v___x_992_);
                v___x_994_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_994_, 0, v___x_993_);
                crate::leanh::lean_ctor_set(v___x_994_, 1, v___x_979_);
                v___x_995_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprRange_repr___redArg___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5,
                );
                v___x_996_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_end_975_);
                v___x_997_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_997_, 0, v___x_995_);
                crate::leanh::lean_ctor_set(v___x_997_, 1, v___x_996_);
                v___x_998_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_998_, 0, v___x_997_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_998_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_985_,
                );
                v___x_999_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_999_, 0, v___x_994_);
                crate::leanh::lean_ctor_set(v___x_999_, 1, v___x_998_);
                v___x_1000_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprPosition_repr___redArg___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13,
                );
                v___x_1001_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__14;
                v___x_1002_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1001_);
                crate::leanh::lean_ctor_set(v___x_1002_, 1, v___x_999_);
                v___x_1003_ = l_Lean_Lsp_instReprPosition_repr___redArg___closed__15;
                v___x_1004_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1002_);
                crate::leanh::lean_ctor_set(v___x_1004_, 1, v___x_1003_);
                v___x_1005_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1005_, 0, v___x_1000_);
                crate::leanh::lean_ctor_set(v___x_1005_, 1, v___x_1004_);
                v___x_1006_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1006_, 0, v___x_1005_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1006_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_985_,
                );
                return v___x_1006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instReprRange_repr(
    mut v_x_1009_: *mut crate::leanh::LeanObject,
    mut v_prec_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Lean_Lsp_instReprRange_repr___redArg(v_x_1009_);
    return v___x_1011_;
}
pub unsafe fn l_Lean_Lsp_instReprRange_repr___boxed(
    mut v_x_1012_: *mut crate::leanh::LeanObject,
    mut v_prec_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l_Lean_Lsp_instReprRange_repr(v_x_1012_, v_prec_1013_);
    crate::leanh::lean_dec(v_prec_1013_);
    return v_res_1014_;
}
pub unsafe fn _init_l_Lean_Lsp_instLTRange() -> *mut crate::leanh::LeanObject {
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = crate::leanh::lean_box(0);
    return v___x_1017_;
}
pub unsafe fn _init_l_Lean_Lsp_instLERange() -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = crate::leanh::lean_box(0);
    return v___x_1018_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_BasicAux(
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
    l_Lean_Lsp_instLTPosition = _init_l_Lean_Lsp_instLTPosition();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instLTPosition);
    l_Lean_Lsp_instLEPosition = _init_l_Lean_Lsp_instLEPosition();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instLEPosition);
    l_Lean_Lsp_instLTRange = _init_l_Lean_Lsp_instLTRange();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instLTRange);
    l_Lean_Lsp_instLERange = _init_l_Lean_Lsp_instLERange();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instLERange);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_BasicAux(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_BasicAux(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Data_Lsp_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_BasicAux(builtin);
}
