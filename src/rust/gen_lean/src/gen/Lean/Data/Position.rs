// Lean compiler output
// Module: Lean.Data.Position
// Imports: Lean.Data.Json.FromToJson.Basic Lean.ToExpr
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub,
    lean_nat_to_int, lean_string_append, lean_string_length, lean_string_utf8_at_end,
    lean_string_utf8_byte_size, lean_string_utf8_get, lean_string_utf8_next, lean_uint32_dec_eq,
};
use crate::r#gen::Init::Core::l_Prod_lexLtDec___aux__1___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_nextn, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Nat_decLt___boxed, l_instDecidableEqNat___boxed};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit};
use crate::r#gen::Lean::ToExpr::{initialize_Lean_ToExpr, runtime_initialize_Lean_ToExpr};
pub static l_Lean_instInhabitedPosition_default___closed__0_value: crate::leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instInhabitedPosition_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPosition_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedPosition_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPosition_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPosition_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_instReprPosition_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__1_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_instReprPosition_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__4_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_instReprPosition_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprPosition_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprPosition_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprPosition_repr___redArg___closed__8_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_instReprPosition_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__10_value:
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
    m_data: [99, 111, 108, 117, 109, 110, 0],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__11_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprPosition_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprPosition_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprPosition_repr___redArg___closed__13_value:
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
static mut l_Lean_instReprPosition_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprPosition_repr___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprPosition_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprPosition_repr___redArg___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprPosition_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprPosition_repr___redArg___closed__16_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition_repr___redArg___closed__17_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprPosition_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprPosition_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPosition___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_instToJsonPosition_toJson___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_instToJsonPosition_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPosition_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToJsonPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonPosition_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instToJsonPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instFromJsonPosition_fromJson___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_instFromJsonPosition_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instFromJsonPosition_fromJson___closed__1_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_instFromJsonPosition_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_instFromJsonPosition_fromJson___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_instFromJsonPosition_fromJson___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7283224396379583297 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instFromJsonPosition_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonPosition_fromJson___closed__4_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_instFromJsonPosition_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instFromJsonPosition_fromJson___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonPosition_fromJson___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7347781233040561197 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instFromJsonPosition_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonPosition_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonPosition_fromJson___closed__9_value: crate::leanh::LeanStringObject<
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
    m_data: [58, 32, 0],
};
static mut l_Lean_instFromJsonPosition_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instFromJsonPosition_fromJson___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonPosition_fromJson___closed__11_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprPosition_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
        8606446320521324977 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instFromJsonPosition_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instFromJsonPosition_fromJson___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonPosition_fromJson___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonPosition_fromJson___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonPosition_fromJson___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonPosition___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonPosition_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonPosition___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instFromJsonPosition: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonPosition___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_lt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_decLt___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Position_lt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_lt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 168, 0],
};
static mut l_Lean_Position_instToFormat___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Position_instToFormat___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___lam__0___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [44, 32, 0],
};
static mut l_Lean_Position_instToFormat___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___lam__0___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Position_instToFormat___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___lam__0___closed__4_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 169, 0],
};
static mut l_Lean_Position_instToFormat___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___lam__0___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Position_instToFormat___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Position_instToFormat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Position_instToFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Position_instToFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Position_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Position_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Position_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Position_instToExpr___lam__0___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [109, 107, 0],
};
static mut l_Lean_Position_instToExpr___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToExpr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instFromJsonPosition_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7283224396379583297 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Position_instToExpr___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Position_instToExpr___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11125062533858197709 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Position_instToExpr___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToExpr___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Position_instToExpr___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Position_instToExpr___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Position_instToExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Position_instToExpr___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Position_instToExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Position_instToExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Position_instToExpr___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Position_instToExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Position_instToExpr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Position_instToExpr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Position_instToExpr: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedFileMap_default___closed__0_value: crate::leanh::LeanStringObject<
    1,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_instInhabitedFileMap_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedFileMap_default___closed__1_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_instInhabitedFileMap_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedFileMap_default___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instInhabitedFileMap_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedFileMap_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedFileMap: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedFileMap_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_FileMap_ofString___closed__0_value: crate::leanh::LeanArrayObject<1> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_FileMap_ofString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_FileMap_ofString___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instDecidableEqPosition_decEq(
    mut v_x_509_: *mut crate::leanh::LeanObject,
    mut v_x_510_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_line_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    v_line_511_ = crate::leanh::lean_ctor_get(v_x_509_, 0);
    v_column_512_ = crate::leanh::lean_ctor_get(v_x_509_, 1);
    v_line_513_ = crate::leanh::lean_ctor_get(v_x_510_, 0);
    v_column_514_ = crate::leanh::lean_ctor_get(v_x_510_, 1);
    v___x_515_ = lean_nat_dec_eq(v_line_511_, v_line_513_);
    if v___x_515_ == 0 {
        return v___x_515_;
    } else {
        let mut v___x_516_: u8 = 0;
        v___x_516_ = lean_nat_dec_eq(v_column_512_, v_column_514_);
        return v___x_516_;
    }
}
pub unsafe fn l_Lean_instDecidableEqPosition_decEq___boxed(
    mut v_x_517_: *mut crate::leanh::LeanObject,
    mut v_x_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_519_: u8 = 0;
    let mut v_r_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_instDecidableEqPosition_decEq(v_x_517_, v_x_518_);
    crate::leanh::lean_dec_ref(v_x_518_);
    crate::leanh::lean_dec_ref(v_x_517_);
    v_r_520_ = crate::leanh::lean_box((v_res_519_) as usize);
    return v_r_520_;
}
pub unsafe fn l_Lean_instDecidableEqPosition(
    mut v_x_521_: *mut crate::leanh::LeanObject,
    mut v_x_522_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_523_: u8 = 0;
    v___x_523_ = l_Lean_instDecidableEqPosition_decEq(v_x_521_, v_x_522_);
    return v___x_523_;
}
pub unsafe fn l_Lean_instDecidableEqPosition___boxed(
    mut v_x_524_: *mut crate::leanh::LeanObject,
    mut v_x_525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_526_: u8 = 0;
    let mut v_r_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Lean_instDecidableEqPosition(v_x_524_, v_x_525_);
    crate::leanh::lean_dec_ref(v_x_525_);
    crate::leanh::lean_dec_ref(v_x_524_);
    v_r_527_ = crate::leanh::lean_box((v_res_526_) as usize);
    return v_r_527_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprPosition_repr_spec__0(
    mut v_a_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = lean_nat_to_int(v_a_528_);
    return v___x_529_;
}
pub unsafe fn _init_l_Lean_instReprPosition_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_544_ = lean_nat_to_int(v___x_543_);
    return v___x_544_;
}
pub unsafe fn _init_l_Lean_instReprPosition_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_552_ = lean_nat_to_int(v___x_551_);
    return v___x_552_;
}
pub unsafe fn _init_l_Lean_instReprPosition_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l_Lean_instReprPosition_repr___redArg___closed__0;
    v___x_555_ = lean_string_length(v___x_554_);
    return v___x_555_;
}
pub unsafe fn _init_l_Lean_instReprPosition_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprPosition_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_instReprPosition_repr___redArg___closed__14_once),
        _init_l_Lean_instReprPosition_repr___redArg___closed__14,
    );
    v___x_557_ = lean_nat_to_int(v___x_556_);
    return v___x_557_;
}
pub unsafe fn l_Lean_instReprPosition_repr___redArg(
    mut v_x_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_567_: u8 = 0;
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_563_ = crate::leanh::lean_ctor_get(v_x_562_, 0);
                v_column_564_ = crate::leanh::lean_ctor_get(v_x_562_, 1);
                v_isSharedCheck_599_ = (!crate::leanh::lean_is_exclusive(v_x_562_)) as u8;
                if v_isSharedCheck_599_ == 0 {
                    v___x_566_ = v_x_562_;
                    v_isShared_567_ = v_isSharedCheck_599_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_564_);
                    crate::leanh::lean_inc(v_line_563_);
                    crate::leanh::lean_dec(v_x_562_);
                    v___x_566_ = crate::leanh::lean_box(0);
                    v_isShared_567_ = v_isSharedCheck_599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_568_ = l_Lean_instReprPosition_repr___redArg___closed__5;
                v___x_569_ = l_Lean_instReprPosition_repr___redArg___closed__6;
                v___x_570_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprPosition_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_instReprPosition_repr___redArg___closed__7_once),
                    _init_l_Lean_instReprPosition_repr___redArg___closed__7,
                );
                v___x_571_ = l_Nat_reprFast(v_line_563_);
                v___x_572_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_572_, 0, v___x_571_);
                if v_isShared_567_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_566_, 4);
                    crate::leanh::lean_ctor_set(v___x_566_, 1, v___x_572_);
                    crate::leanh::lean_ctor_set(v___x_566_, 0, v___x_570_);
                    v___x_574_ = v___x_566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_598_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_572_);
                    v___x_574_ = v_reuseFailAlloc_598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_575_ = 0;
                v___x_576_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_574_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_576_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_575_,
                );
                v___x_577_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_577_, 0, v___x_569_);
                crate::leanh::lean_ctor_set(v___x_577_, 1, v___x_576_);
                v___x_578_ = l_Lean_instReprPosition_repr___redArg___closed__9;
                v___x_579_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_577_);
                crate::leanh::lean_ctor_set(v___x_579_, 1, v___x_578_);
                v___x_580_ = crate::leanh::lean_box(1);
                v___x_581_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_581_, 0, v___x_579_);
                crate::leanh::lean_ctor_set(v___x_581_, 1, v___x_580_);
                v___x_582_ = l_Lean_instReprPosition_repr___redArg___closed__11;
                v___x_583_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_581_);
                crate::leanh::lean_ctor_set(v___x_583_, 1, v___x_582_);
                v___x_584_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_583_);
                crate::leanh::lean_ctor_set(v___x_584_, 1, v___x_568_);
                v___x_585_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprPosition_repr___redArg___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprPosition_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_instReprPosition_repr___redArg___closed__12,
                );
                v___x_586_ = l_Nat_reprFast(v_column_564_);
                v___x_587_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_587_, 0, v___x_586_);
                v___x_588_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_588_, 0, v___x_585_);
                crate::leanh::lean_ctor_set(v___x_588_, 1, v___x_587_);
                v___x_589_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_589_, 0, v___x_588_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_589_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_575_,
                );
                v___x_590_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_590_, 0, v___x_584_);
                crate::leanh::lean_ctor_set(v___x_590_, 1, v___x_589_);
                v___x_591_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprPosition_repr___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprPosition_repr___redArg___closed__15_once
                    ),
                    _init_l_Lean_instReprPosition_repr___redArg___closed__15,
                );
                v___x_592_ = l_Lean_instReprPosition_repr___redArg___closed__16;
                v___x_593_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_593_, 0, v___x_592_);
                crate::leanh::lean_ctor_set(v___x_593_, 1, v___x_590_);
                v___x_594_ = l_Lean_instReprPosition_repr___redArg___closed__17;
                v___x_595_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_595_, 0, v___x_593_);
                crate::leanh::lean_ctor_set(v___x_595_, 1, v___x_594_);
                v___x_596_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_596_, 0, v___x_591_);
                crate::leanh::lean_ctor_set(v___x_596_, 1, v___x_595_);
                v___x_597_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_597_, 0, v___x_596_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_597_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_575_,
                );
                return v___x_597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprPosition_repr(
    mut v_x_600_: *mut crate::leanh::LeanObject,
    mut v_prec_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = l_Lean_instReprPosition_repr___redArg(v_x_600_);
    return v___x_602_;
}
pub unsafe fn l_Lean_instReprPosition_repr___boxed(
    mut v_x_603_: *mut crate::leanh::LeanObject,
    mut v_prec_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_605_ = l_Lean_instReprPosition_repr(v_x_603_, v_prec_604_);
    crate::leanh::lean_dec(v_prec_604_);
    return v_res_605_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(
    mut v_a_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_608_) == 0 {
                    v___x_610_ = lean_array_to_list(v_a_609_);
                    return v___x_610_;
                } else {
                    v_head_611_ = crate::leanh::lean_ctor_get(v_a_608_, 0);
                    crate::leanh::lean_inc(v_head_611_);
                    v_tail_612_ = crate::leanh::lean_ctor_get(v_a_608_, 1);
                    crate::leanh::lean_inc(v_tail_612_);
                    crate::leanh::lean_dec_ref_known(v_a_608_, 2);
                    v___x_613_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_609_,
                        v_head_611_,
                    );
                    v_a_608_ = v_tail_612_;
                    v_a_609_ = v___x_613_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonPosition_toJson(
    mut v_x_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_618_ = crate::leanh::lean_ctor_get(v_x_617_, 0);
                v_column_619_ = crate::leanh::lean_ctor_get(v_x_617_, 1);
                v_isSharedCheck_641_ = (!crate::leanh::lean_is_exclusive(v_x_617_)) as u8;
                if v_isSharedCheck_641_ == 0 {
                    v___x_621_ = v_x_617_;
                    v_isShared_622_ = v_isSharedCheck_641_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_619_);
                    crate::leanh::lean_inc(v_line_618_);
                    crate::leanh::lean_dec(v_x_617_);
                    v___x_621_ = crate::leanh::lean_box(0);
                    v_isShared_622_ = v_isSharedCheck_641_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_623_ = l_Lean_instReprPosition_repr___redArg___closed__1;
                v___x_624_ = l_Lean_JsonNumber_fromNat(v_line_618_);
                v___x_625_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_625_, 0, v___x_624_);
                if v_isShared_622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_621_, 1, v___x_625_);
                    crate::leanh::lean_ctor_set(v___x_621_, 0, v___x_623_);
                    v___x_627_ = v___x_621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_640_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_625_);
                    v___x_627_ = v_reuseFailAlloc_640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_628_ = crate::leanh::lean_box(0);
                v___x_629_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_629_, 0, v___x_627_);
                crate::leanh::lean_ctor_set(v___x_629_, 1, v___x_628_);
                v___x_630_ = l_Lean_instReprPosition_repr___redArg___closed__10;
                v___x_631_ = l_Lean_JsonNumber_fromNat(v_column_619_);
                v___x_632_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_632_, 0, v___x_631_);
                v___x_633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_633_, 0, v___x_630_);
                crate::leanh::lean_ctor_set(v___x_633_, 1, v___x_632_);
                v___x_634_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_634_, 0, v___x_633_);
                crate::leanh::lean_ctor_set(v___x_634_, 1, v___x_628_);
                v___x_635_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_635_, 0, v___x_634_);
                crate::leanh::lean_ctor_set(v___x_635_, 1, v___x_628_);
                v___x_636_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_629_);
                crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_635_);
                v___x_637_ = l_Lean_instToJsonPosition_toJson___closed__0;
                v___x_638_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(v___x_636_, v___x_637_);
                v___x_639_ = l_Lean_Json_mkObj(v___x_638_);
                crate::leanh::lean_dec(v___x_638_);
                return v___x_639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(
    mut v_j_644_: *mut crate::leanh::LeanObject,
    mut v_k_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = l_Lean_Json_getObjValD(v_j_644_, v_k_645_);
    v___x_647_ = l_Lean_Json_getNat_x3f(v___x_646_);
    return v___x_647_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0___boxed(
    mut v_j_648_: *mut crate::leanh::LeanObject,
    mut v_k_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_650_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(
        v_j_648_, v_k_649_,
    );
    crate::leanh::lean_dec_ref(v_k_649_);
    return v_res_650_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = 1;
    v___x_657_ = l_Lean_instFromJsonPosition_fromJson___closed__2;
    v___x_658_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_657_, v___x_656_);
    return v___x_658_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_660_ = l_Lean_instFromJsonPosition_fromJson___closed__4;
    v___x_661_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__3,
    );
    v___x_662_ = lean_string_append(v___x_661_, v___x_660_);
    return v___x_662_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_665_: u8 = 0;
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_665_ = 1;
    v___x_666_ = l_Lean_instFromJsonPosition_fromJson___closed__6;
    v___x_667_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_666_, v___x_665_);
    return v___x_667_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__7_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__7,
    );
    v___x_669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__5,
    );
    v___x_670_ = lean_string_append(v___x_669_, v___x_668_);
    return v___x_670_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = l_Lean_instFromJsonPosition_fromJson___closed__9;
    v___x_673_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__8_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__8,
    );
    v___x_674_ = lean_string_append(v___x_673_, v___x_672_);
    return v___x_674_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = 1;
    v___x_678_ = l_Lean_instFromJsonPosition_fromJson___closed__11;
    v___x_679_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_678_, v___x_677_);
    return v___x_679_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__12_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__12,
    );
    v___x_681_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__5,
    );
    v___x_682_ = lean_string_append(v___x_681_, v___x_680_);
    return v___x_682_;
}
pub unsafe fn _init_l_Lean_instFromJsonPosition_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_instFromJsonPosition_fromJson___closed__9;
    v___x_684_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__13_once),
        _init_l_Lean_instFromJsonPosition_fromJson___closed__13,
    );
    v___x_685_ = lean_string_append(v___x_684_, v___x_683_);
    return v___x_685_;
}
pub unsafe fn l_Lean_instFromJsonPosition_fromJson(
    mut v_json_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_692_: u8 = 0;
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_698_: u8 = 0;
    let mut v_a_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_702_: u8 = 0;
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_706_: u8 = 0;
    let mut v_a_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_713_: u8 = 0;
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_719_: u8 = 0;
    let mut v_a_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_723_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut v_a_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_731_: u8 = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_687_ = l_Lean_instReprPosition_repr___redArg___closed__1;
                crate::leanh::lean_inc(v_json_686_);
                v___x_688_ =
                    l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(
                        v_json_686_,
                        v___x_687_,
                    );
                if crate::leanh::lean_obj_tag(v___x_688_) == 0 {
                    crate::leanh::lean_dec(v_json_686_);
                    v_a_689_ = crate::leanh::lean_ctor_get(v___x_688_, 0);
                    v_isSharedCheck_698_ = (!crate::leanh::lean_is_exclusive(v___x_688_)) as u8;
                    if v_isSharedCheck_698_ == 0 {
                        v___x_691_ = v___x_688_;
                        v_isShared_692_ = v_isSharedCheck_698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_689_);
                        crate::leanh::lean_dec(v___x_688_);
                        v___x_691_ = crate::leanh::lean_box(0);
                        v_isShared_692_ = v_isSharedCheck_698_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_688_) == 0 {
                        crate::leanh::lean_dec(v_json_686_);
                        v_a_699_ = crate::leanh::lean_ctor_get(v___x_688_, 0);
                        v_isSharedCheck_706_ = (!crate::leanh::lean_is_exclusive(v___x_688_)) as u8;
                        if v_isSharedCheck_706_ == 0 {
                            v___x_701_ = v___x_688_;
                            v_isShared_702_ = v_isSharedCheck_706_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_699_);
                            crate::leanh::lean_dec(v___x_688_);
                            v___x_701_ = crate::leanh::lean_box(0);
                            v_isShared_702_ = v_isSharedCheck_706_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_707_ = crate::leanh::lean_ctor_get(v___x_688_, 0);
                        crate::leanh::lean_inc(v_a_707_);
                        crate::leanh::lean_dec_ref_known(v___x_688_, 1);
                        v___x_708_ = l_Lean_instReprPosition_repr___redArg___closed__10;
                        v___x_709_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_json_686_, v___x_708_);
                        if crate::leanh::lean_obj_tag(v___x_709_) == 0 {
                            crate::leanh::lean_dec(v_a_707_);
                            v_a_710_ = crate::leanh::lean_ctor_get(v___x_709_, 0);
                            v_isSharedCheck_719_ =
                                (!crate::leanh::lean_is_exclusive(v___x_709_)) as u8;
                            if v_isSharedCheck_719_ == 0 {
                                v___x_712_ = v___x_709_;
                                v_isShared_713_ = v_isSharedCheck_719_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_710_);
                                crate::leanh::lean_dec(v___x_709_);
                                v___x_712_ = crate::leanh::lean_box(0);
                                v_isShared_713_ = v_isSharedCheck_719_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_709_) == 0 {
                                crate::leanh::lean_dec(v_a_707_);
                                v_a_720_ = crate::leanh::lean_ctor_get(v___x_709_, 0);
                                v_isSharedCheck_727_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_709_)) as u8;
                                if v_isSharedCheck_727_ == 0 {
                                    v___x_722_ = v___x_709_;
                                    v_isShared_723_ = v_isSharedCheck_727_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_720_);
                                    crate::leanh::lean_dec(v___x_709_);
                                    v___x_722_ = crate::leanh::lean_box(0);
                                    v_isShared_723_ = v_isSharedCheck_727_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_728_ = crate::leanh::lean_ctor_get(v___x_709_, 0);
                                v_isSharedCheck_736_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_709_)) as u8;
                                if v_isSharedCheck_736_ == 0 {
                                    v___x_730_ = v___x_709_;
                                    v_isShared_731_ = v_isSharedCheck_736_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_728_);
                                    crate::leanh::lean_dec(v___x_709_);
                                    v___x_730_ = crate::leanh::lean_box(0);
                                    v_isShared_731_ = v_isSharedCheck_736_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_693_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__10_once),
                    _init_l_Lean_instFromJsonPosition_fromJson___closed__10,
                );
                v___x_694_ = lean_string_append(v___x_693_, v_a_689_);
                crate::leanh::lean_dec(v_a_689_);
                if v_isShared_692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_691_, 0, v___x_694_);
                    v___x_696_ = v___x_691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
                    v___x_696_ = v_reuseFailAlloc_697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_696_;
            }
            3 => {
                if v_isShared_702_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_701_, 0);
                    v___x_704_ = v___x_701_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
                    v___x_704_ = v_reuseFailAlloc_705_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_704_;
            }
            5 => {
                v___x_714_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonPosition_fromJson___closed__14_once),
                    _init_l_Lean_instFromJsonPosition_fromJson___closed__14,
                );
                v___x_715_ = lean_string_append(v___x_714_, v_a_710_);
                crate::leanh::lean_dec(v_a_710_);
                if v_isShared_713_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_712_, 0, v___x_715_);
                    v___x_717_ = v___x_712_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
                    v___x_717_ = v_reuseFailAlloc_718_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_717_;
            }
            7 => {
                if v_isShared_723_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_722_, 0);
                    v___x_725_ = v___x_722_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
                    v___x_725_ = v_reuseFailAlloc_726_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_725_;
            }
            9 => {
                v___x_732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_732_, 0, v_a_707_);
                crate::leanh::lean_ctor_set(v___x_732_, 1, v_a_728_);
                if v_isShared_731_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_730_, 0, v___x_732_);
                    v___x_734_ = v___x_730_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
                    v___x_734_ = v_reuseFailAlloc_735_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Position_lt(
    mut v_x_740_: *mut crate::leanh::LeanObject,
    mut v_x_741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_line_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v_line_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_751_: u8 = 0;
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    let mut v_reuseFailAlloc_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut v_isSharedCheck_762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_742_ = crate::leanh::lean_ctor_get(v_x_740_, 0);
                v_column_743_ = crate::leanh::lean_ctor_get(v_x_740_, 1);
                v_isSharedCheck_762_ = (!crate::leanh::lean_is_exclusive(v_x_740_)) as u8;
                if v_isSharedCheck_762_ == 0 {
                    v___x_745_ = v_x_740_;
                    v_isShared_746_ = v_isSharedCheck_762_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_743_);
                    crate::leanh::lean_inc(v_line_742_);
                    crate::leanh::lean_dec(v_x_740_);
                    v___x_745_ = crate::leanh::lean_box(0);
                    v_isShared_746_ = v_isSharedCheck_762_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_line_747_ = crate::leanh::lean_ctor_get(v_x_741_, 0);
                v_column_748_ = crate::leanh::lean_ctor_get(v_x_741_, 1);
                v_isSharedCheck_761_ = (!crate::leanh::lean_is_exclusive(v_x_741_)) as u8;
                if v_isSharedCheck_761_ == 0 {
                    v___x_750_ = v_x_741_;
                    v_isShared_751_ = v_isSharedCheck_761_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_748_);
                    crate::leanh::lean_inc(v_line_747_);
                    crate::leanh::lean_dec(v_x_741_);
                    v___x_750_ = crate::leanh::lean_box(0);
                    v_isShared_751_ = v_isSharedCheck_761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_752_ = crate::leanh::lean_alloc_closure(
                    l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
                    2,
                    0,
                );
                v___x_753_ = l_Lean_Position_lt___closed__0;
                if v_isShared_751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_750_, 1, v_column_743_);
                    crate::leanh::lean_ctor_set(v___x_750_, 0, v_line_742_);
                    v___x_755_ = v___x_750_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 0, v_line_742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 1, v_column_743_);
                    v___x_755_ = v_reuseFailAlloc_760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_745_, 1, v_column_748_);
                    crate::leanh::lean_ctor_set(v___x_745_, 0, v_line_747_);
                    v___x_757_ = v___x_745_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 0, v_line_747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_759_, 1, v_column_748_);
                    v___x_757_ = v_reuseFailAlloc_759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_758_ = l_Prod_lexLtDec___aux__1___redArg(
                    v___x_752_, v___x_753_, v___x_753_, v___x_755_, v___x_757_,
                );
                return v___x_758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Position_lt___boxed(
    mut v_x_763_: *mut crate::leanh::LeanObject,
    mut v_x_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Lean_Position_lt(v_x_763_, v_x_764_);
    v_r_766_ = crate::leanh::lean_box((v_res_765_) as usize);
    return v_r_766_;
}
pub unsafe fn l_Lean_Position_instToFormat___lam__0(
    mut v_x_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_777_ = crate::leanh::lean_ctor_get(v_x_776_, 0);
                v_column_778_ = crate::leanh::lean_ctor_get(v_x_776_, 1);
                v_isSharedCheck_795_ = (!crate::leanh::lean_is_exclusive(v_x_776_)) as u8;
                if v_isSharedCheck_795_ == 0 {
                    v___x_780_ = v_x_776_;
                    v_isShared_781_ = v_isSharedCheck_795_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_778_);
                    crate::leanh::lean_inc(v_line_777_);
                    crate::leanh::lean_dec(v_x_776_);
                    v___x_780_ = crate::leanh::lean_box(0);
                    v_isShared_781_ = v_isSharedCheck_795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_782_ = l_Lean_Position_instToFormat___lam__0___closed__1;
                v___x_783_ = l_Nat_reprFast(v_line_777_);
                v___x_784_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_784_, 0, v___x_783_);
                if v_isShared_781_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_780_, 5);
                    crate::leanh::lean_ctor_set(v___x_780_, 1, v___x_784_);
                    crate::leanh::lean_ctor_set(v___x_780_, 0, v___x_782_);
                    v___x_786_ = v___x_780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_794_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_784_);
                    v___x_786_ = v_reuseFailAlloc_794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_787_ = l_Lean_Position_instToFormat___lam__0___closed__3;
                v___x_788_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_786_);
                crate::leanh::lean_ctor_set(v___x_788_, 1, v___x_787_);
                v___x_789_ = l_Nat_reprFast(v_column_778_);
                v___x_790_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_790_, 0, v___x_789_);
                v___x_791_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_791_, 0, v___x_788_);
                crate::leanh::lean_ctor_set(v___x_791_, 1, v___x_790_);
                v___x_792_ = l_Lean_Position_instToFormat___lam__0___closed__5;
                v___x_793_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_791_);
                crate::leanh::lean_ctor_set(v___x_793_, 1, v___x_792_);
                return v___x_793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Position_instToString___lam__0(
    mut v_x_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_line_799_ = crate::leanh::lean_ctor_get(v_x_798_, 0);
    crate::leanh::lean_inc(v_line_799_);
    v_column_800_ = crate::leanh::lean_ctor_get(v_x_798_, 1);
    crate::leanh::lean_inc(v_column_800_);
    crate::leanh::lean_dec_ref(v_x_798_);
    v___x_801_ = l_Lean_Position_instToFormat___lam__0___closed__0;
    v___x_802_ = l_Nat_reprFast(v_line_799_);
    v___x_803_ = lean_string_append(v___x_801_, v___x_802_);
    crate::leanh::lean_dec_ref(v___x_802_);
    v___x_804_ = l_Lean_Position_instToFormat___lam__0___closed__2;
    v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
    v___x_806_ = l_Nat_reprFast(v_column_800_);
    v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
    crate::leanh::lean_dec_ref(v___x_806_);
    v___x_808_ = l_Lean_Position_instToFormat___lam__0___closed__4;
    v___x_809_ = lean_string_append(v___x_807_, v___x_808_);
    return v___x_809_;
}
pub unsafe fn _init_l_Lean_Position_instToExpr___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = crate::leanh::lean_box(0);
    v___x_818_ = l_Lean_Position_instToExpr___lam__0___closed__1;
    v___x_819_ = l_Lean_mkConst(v___x_818_, v___x_817_);
    return v___x_819_;
}
pub unsafe fn l_Lean_Position_instToExpr___lam__0(
    mut v_p_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_line_821_ = crate::leanh::lean_ctor_get(v_p_820_, 0);
    crate::leanh::lean_inc(v_line_821_);
    v_column_822_ = crate::leanh::lean_ctor_get(v_p_820_, 1);
    crate::leanh::lean_inc(v_column_822_);
    crate::leanh::lean_dec_ref(v_p_820_);
    v___x_823_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Position_instToExpr___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Position_instToExpr___lam__0___closed__2_once),
        _init_l_Lean_Position_instToExpr___lam__0___closed__2,
    );
    v___x_824_ = l_Lean_mkNatLit(v_line_821_);
    v___x_825_ = l_Lean_mkNatLit(v_column_822_);
    v___x_826_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
    v___x_828_ = lean_array_push(v___x_827_, v___x_824_);
    v___x_829_ = lean_array_push(v___x_828_, v___x_825_);
    v___x_830_ = l_Lean_mkAppN(v___x_823_, v___x_829_);
    crate::leanh::lean_dec_ref(v___x_829_);
    return v___x_830_;
}
pub unsafe fn _init_l_Lean_Position_instToExpr___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = crate::leanh::lean_box(0);
    v___x_833_ = l_Lean_instFromJsonPosition_fromJson___closed__2;
    v___x_834_ = l_Lean_mkConst(v___x_833_, v___x_832_);
    return v___x_834_;
}
pub unsafe fn _init_l_Lean_Position_instToExpr___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Position_instToExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Position_instToExpr___closed__1_once),
        _init_l_Lean_Position_instToExpr___closed__1,
    );
    v___f_836_ = l_Lean_Position_instToExpr___closed__0;
    v___x_837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_837_, 0, v___f_836_);
    crate::leanh::lean_ctor_set(v___x_837_, 1, v___x_835_);
    return v___x_837_;
}
pub unsafe fn _init_l_Lean_Position_instToExpr() -> *mut crate::leanh::LeanObject {
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Position_instToExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Position_instToExpr___closed__2_once),
        _init_l_Lean_Position_instToExpr___closed__2,
    );
    return v___x_838_;
}
pub unsafe fn l_Lean_FileMap_getLastLine(
    mut v_fmap_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_positions_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_positions_848_ = crate::leanh::lean_ctor_get(v_fmap_847_, 1);
    v___x_849_ = lean_array_get_size(v_positions_848_);
    v___x_850_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_851_ = lean_nat_sub(v___x_849_, v___x_850_);
    return v___x_851_;
}
pub unsafe fn l_Lean_FileMap_getLastLine___boxed(
    mut v_fmap_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Lean_FileMap_getLastLine(v_fmap_852_);
    crate::leanh::lean_dec_ref(v_fmap_852_);
    return v_res_853_;
}
pub unsafe fn l_Lean_FileMap_getLine(
    mut v_fmap_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u8 = 0;
    v___x_856_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_857_ = lean_nat_add(v_x_855_, v___x_856_);
    v___x_858_ = l_Lean_FileMap_getLastLine(v_fmap_854_);
    v___x_859_ = lean_nat_dec_le(v___x_857_, v___x_858_);
    if v___x_859_ == 0 {
        crate::leanh::lean_dec(v___x_857_);
        return v___x_858_;
    } else {
        crate::leanh::lean_dec(v___x_858_);
        return v___x_857_;
    }
}
pub unsafe fn l_Lean_FileMap_getLine___boxed(
    mut v_fmap_860_: *mut crate::leanh::LeanObject,
    mut v_x_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l_Lean_FileMap_getLine(v_fmap_860_, v_x_861_);
    crate::leanh::lean_dec(v_x_861_);
    crate::leanh::lean_dec_ref(v_fmap_860_);
    return v_res_862_;
}
pub unsafe fn l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(
    mut v_s_863_: *mut crate::leanh::LeanObject,
    mut v_i_864_: *mut crate::leanh::LeanObject,
    mut v_ps_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_866_: u8 = 0;
    let mut v_c_867_: u32 = 0;
    let mut v_i_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u32 = 0;
    let mut v___x_870_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_866_ = lean_string_utf8_at_end(v_s_863_, v_i_864_);
                if v___x_866_ == 0 {
                    v_c_867_ = lean_string_utf8_get(v_s_863_, v_i_864_);
                    v_i_868_ = lean_string_utf8_next(v_s_863_, v_i_864_);
                    crate::leanh::lean_dec(v_i_864_);
                    v___x_869_ = 10;
                    v___x_870_ = lean_uint32_dec_eq(v_c_867_, v___x_869_);
                    if v___x_870_ == 0 {
                        v_i_864_ = v_i_868_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_868_);
                        v___x_872_ = lean_array_push(v_ps_865_, v_i_868_);
                        v_i_864_ = v_i_868_;
                        v_ps_865_ = v___x_872_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_874_ = lean_array_push(v_ps_865_, v_i_864_);
                    v___x_875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_875_, 0, v_s_863_);
                    crate::leanh::lean_ctor_set(v___x_875_, 1, v___x_874_);
                    return v___x_875_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_ofString(
    mut v_s_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_882_ = l_Lean_FileMap_ofString___closed__0;
    v___x_883_ = l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(
        v_s_880_, v___x_881_, v___x_882_,
    );
    return v___x_883_;
}
pub unsafe fn l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(
    mut v_pos_884_: *mut crate::leanh::LeanObject,
    mut v_str_885_: *mut crate::leanh::LeanObject,
    mut v_i_886_: *mut crate::leanh::LeanObject,
    mut v_c_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_889_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    let mut v___x_895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_894_ = lean_nat_dec_eq(v_i_886_, v_pos_884_);
                if v___x_894_ == 0 {
                    v___x_895_ = lean_string_utf8_at_end(v_str_885_, v_i_886_);
                    v___y_889_ = v___x_895_;
                    state = 1;
                    continue;
                } else {
                    v___y_889_ = v___x_894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_889_ == 0 {
                    v___x_890_ = lean_string_utf8_next(v_str_885_, v_i_886_);
                    crate::leanh::lean_dec(v_i_886_);
                    v___x_891_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_892_ = lean_nat_add(v_c_887_, v___x_891_);
                    crate::leanh::lean_dec(v_c_887_);
                    v_i_886_ = v___x_890_;
                    v_c_887_ = v___x_892_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_i_886_);
                    return v_c_887_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn___boxed(
    mut v_pos_896_: *mut crate::leanh::LeanObject,
    mut v_str_897_: *mut crate::leanh::LeanObject,
    mut v_i_898_: *mut crate::leanh::LeanObject,
    mut v_c_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_900_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(
        v_pos_896_, v_str_897_, v_i_898_, v_c_899_,
    );
    crate::leanh::lean_dec_ref(v_str_897_);
    crate::leanh::lean_dec(v_pos_896_);
    return v_res_900_;
}
pub unsafe fn l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(
    mut v_fmap_901_: *mut crate::leanh::LeanObject,
    mut v_pos_902_: *mut crate::leanh::LeanObject,
    mut v_str_903_: *mut crate::leanh::LeanObject,
    mut v_ps_904_: *mut crate::leanh::LeanObject,
    mut v_b_905_: *mut crate::leanh::LeanObject,
    mut v_e_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: u8 = 0;
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_posM_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_posB_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_907_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_908_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_909_ = lean_nat_add(v_b_905_, v___x_908_);
                v___x_910_ = lean_nat_dec_eq(v_e_906_, v___x_909_);
                crate::leanh::lean_dec(v___x_909_);
                if v___x_910_ == 0 {
                    v___x_911_ = lean_nat_add(v_b_905_, v_e_906_);
                    v_m_912_ = lean_nat_shiftr(v___x_911_, v___x_908_);
                    crate::leanh::lean_dec(v___x_911_);
                    v_posM_913_ = lean_array_get_borrowed(v___x_907_, v_ps_904_, v_m_912_);
                    v___x_914_ = lean_nat_dec_eq(v_pos_902_, v_posM_913_);
                    if v___x_914_ == 0 {
                        v___x_915_ = lean_nat_dec_lt(v_posM_913_, v_pos_902_);
                        if v___x_915_ == 0 {
                            crate::leanh::lean_dec(v_e_906_);
                            v_e_906_ = v_m_912_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_905_);
                            v_b_905_ = v_m_912_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_e_906_);
                        crate::leanh::lean_dec(v_b_905_);
                        v___x_918_ = l_Lean_FileMap_getLine(v_fmap_901_, v_m_912_);
                        crate::leanh::lean_dec(v_m_912_);
                        v___x_919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_918_);
                        crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_907_);
                        return v___x_919_;
                    }
                } else {
                    crate::leanh::lean_dec(v_e_906_);
                    v_posB_920_ = lean_array_get_borrowed(v___x_907_, v_ps_904_, v_b_905_);
                    v___x_921_ = l_Lean_FileMap_getLine(v_fmap_901_, v_b_905_);
                    crate::leanh::lean_dec(v_b_905_);
                    crate::leanh::lean_inc(v_posB_920_);
                    v___x_922_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(
                        v_pos_902_,
                        v_str_903_,
                        v_posB_920_,
                        v___x_907_,
                    );
                    v___x_923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
                    crate::leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
                    return v___x_923_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop___boxed(
    mut v_fmap_924_: *mut crate::leanh::LeanObject,
    mut v_pos_925_: *mut crate::leanh::LeanObject,
    mut v_str_926_: *mut crate::leanh::LeanObject,
    mut v_ps_927_: *mut crate::leanh::LeanObject,
    mut v_b_928_: *mut crate::leanh::LeanObject,
    mut v_e_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_930_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(
        v_fmap_924_,
        v_pos_925_,
        v_str_926_,
        v_ps_927_,
        v_b_928_,
        v_e_929_,
    );
    crate::leanh::lean_dec_ref(v_ps_927_);
    crate::leanh::lean_dec_ref(v_str_926_);
    crate::leanh::lean_dec(v_pos_925_);
    crate::leanh::lean_dec_ref(v_fmap_924_);
    return v_res_930_;
}
pub unsafe fn l_Lean_FileMap_toPosition(
    mut v_fmap_931_: *mut crate::leanh::LeanObject,
    mut v_pos_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_source_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_positions_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_939_: u8 = 0;
    let mut v___x_940_: u8 = 0;
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut v_unused_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_source_933_ = crate::leanh::lean_ctor_get(v_fmap_931_, 0);
                v_positions_934_ = crate::leanh::lean_ctor_get(v_fmap_931_, 1);
                crate::leanh::lean_inc_ref(v_positions_934_);
                v___x_935_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_936_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_937_ = lean_array_get_size(v_positions_934_);
                v___x_959_ = lean_nat_dec_le(v___x_936_, v___x_937_);
                if v___x_959_ == 0 {
                    v___y_939_ = v___x_959_;
                    state = 1;
                    continue;
                } else {
                    v___x_960_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_961_ = lean_nat_sub(v___x_937_, v___x_960_);
                    v___x_962_ = lean_array_get_borrowed(v___x_935_, v_positions_934_, v___x_961_);
                    crate::leanh::lean_dec(v___x_961_);
                    v___x_963_ = lean_nat_dec_le(v_pos_932_, v___x_962_);
                    v___y_939_ = v___x_963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_939_ == 0 {
                    v___x_940_ = lean_nat_dec_eq(v___x_937_, v___x_935_);
                    if v___x_940_ == 0 {
                        v___x_941_ = l_Lean_FileMap_getLastLine(v_fmap_931_);
                        v_isSharedCheck_952_ =
                            (!crate::leanh::lean_is_exclusive(v_fmap_931_)) as u8;
                        if v_isSharedCheck_952_ == 0 {
                            v_unused_953_ = crate::leanh::lean_ctor_get(v_fmap_931_, 1);
                            crate::leanh::lean_dec(v_unused_953_);
                            v_unused_954_ = crate::leanh::lean_ctor_get(v_fmap_931_, 0);
                            crate::leanh::lean_dec(v_unused_954_);
                            v___x_943_ = v_fmap_931_;
                            v_isShared_944_ = v_isSharedCheck_952_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fmap_931_);
                            v___x_943_ = crate::leanh::lean_box(0);
                            v_isShared_944_ = v_isSharedCheck_952_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_positions_934_);
                        crate::leanh::lean_dec_ref(v_fmap_931_);
                        v___x_955_ = l_Lean_instInhabitedPosition_default___closed__0;
                        return v___x_955_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_source_933_);
                    v___x_956_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_957_ = lean_nat_sub(v___x_937_, v___x_956_);
                    v___x_958_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(
                        v_fmap_931_,
                        v_pos_932_,
                        v_source_933_,
                        v_positions_934_,
                        v___x_935_,
                        v___x_957_,
                    );
                    crate::leanh::lean_dec_ref(v_positions_934_);
                    crate::leanh::lean_dec_ref(v_source_933_);
                    crate::leanh::lean_dec_ref(v_fmap_931_);
                    return v___x_958_;
                }
            }
            2 => {
                v___x_945_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_946_ = lean_nat_sub(v___x_937_, v___x_945_);
                v___x_947_ = lean_array_get(v___x_935_, v_positions_934_, v___x_946_);
                crate::leanh::lean_dec(v___x_946_);
                crate::leanh::lean_dec_ref(v_positions_934_);
                v___x_948_ = lean_nat_sub(v_pos_932_, v___x_947_);
                crate::leanh::lean_dec(v___x_947_);
                if v_isShared_944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_943_, 1, v___x_948_);
                    crate::leanh::lean_ctor_set(v___x_943_, 0, v___x_941_);
                    v___x_950_ = v___x_943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
                    v___x_950_ = v_reuseFailAlloc_951_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_toPosition___boxed(
    mut v_fmap_964_: *mut crate::leanh::LeanObject,
    mut v_pos_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_FileMap_toPosition(v_fmap_964_, v_pos_965_);
    crate::leanh::lean_dec(v_pos_965_);
    return v_res_966_;
}
pub unsafe fn l_Lean_FileMap_ofPosition(
    mut v_text_967_: *mut crate::leanh::LeanObject,
    mut v_pos_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_positions_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_969_ = crate::leanh::lean_ctor_get(v_pos_968_, 0);
                crate::leanh::lean_inc(v_line_969_);
                v_column_970_ = crate::leanh::lean_ctor_get(v_pos_968_, 1);
                crate::leanh::lean_inc(v_column_970_);
                crate::leanh::lean_dec_ref(v_pos_968_);
                v_source_971_ = crate::leanh::lean_ctor_get(v_text_967_, 0);
                v_positions_972_ = crate::leanh::lean_ctor_get(v_text_967_, 1);
                v___x_980_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_981_ = lean_nat_sub(v_line_969_, v___x_980_);
                crate::leanh::lean_dec(v_line_969_);
                v___x_982_ = lean_array_get_size(v_positions_972_);
                v___x_983_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
                if v___x_983_ == 0 {
                    crate::leanh::lean_dec(v___x_981_);
                    v___x_984_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_985_ = lean_nat_dec_eq(v___x_982_, v___x_984_);
                    if v___x_985_ == 0 {
                        v___x_986_ = lean_nat_sub(v___x_982_, v___x_980_);
                        v___x_987_ =
                            lean_array_get_borrowed(v___x_984_, v_positions_972_, v___x_986_);
                        crate::leanh::lean_dec(v___x_986_);
                        v___y_974_ = v___x_987_;
                        state = 1;
                        continue;
                    } else {
                        v___y_974_ = v___x_984_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_988_ = lean_array_fget_borrowed(v_positions_972_, v___x_981_);
                    crate::leanh::lean_dec(v___x_981_);
                    v___y_974_ = v___x_988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_975_ = lean_string_utf8_byte_size(v_source_971_);
                v___x_976_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_source_971_);
                v___x_977_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_977_, 0, v_source_971_);
                crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_976_);
                crate::leanh::lean_ctor_set(v___x_977_, 2, v___x_975_);
                v___x_978_ = l_String_Slice_pos_x21(v___x_977_, v___y_974_);
                v___x_979_ = l_String_Slice_Pos_nextn(v___x_977_, v___x_978_, v_column_970_);
                crate::leanh::lean_dec_ref_known(v___x_977_, 3);
                return v___x_979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_ofPosition___boxed(
    mut v_text_989_: *mut crate::leanh::LeanObject,
    mut v_pos_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lean_FileMap_ofPosition(v_text_989_, v_pos_990_);
    crate::leanh::lean_dec_ref(v_text_989_);
    return v_res_991_;
}
pub unsafe fn l_Lean_FileMap_lineStart(
    mut v_map_992_: *mut crate::leanh::LeanObject,
    mut v_line_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_positions_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: u8 = 0;
    v_positions_994_ = crate::leanh::lean_ctor_get(v_map_992_, 1);
    v___x_995_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_996_ = lean_nat_sub(v_line_993_, v___x_995_);
    v___x_997_ = lean_array_get_size(v_positions_994_);
    v___x_998_ = lean_nat_dec_lt(v___x_996_, v___x_997_);
    if v___x_998_ == 0 {
        let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: u8 = 0;
        crate::leanh::lean_dec(v___x_996_);
        v___x_999_ = lean_nat_sub(v___x_997_, v___x_995_);
        v___x_1000_ = lean_nat_dec_lt(v___x_999_, v___x_997_);
        if v___x_1000_ == 0 {
            let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_999_);
            v___x_1001_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1001_;
        } else {
            let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1002_ = lean_array_fget_borrowed(v_positions_994_, v___x_999_);
            crate::leanh::lean_dec(v___x_999_);
            crate::leanh::lean_inc(v___x_1002_);
            return v___x_1002_;
        }
    } else {
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1003_ = lean_array_fget_borrowed(v_positions_994_, v___x_996_);
        crate::leanh::lean_dec(v___x_996_);
        crate::leanh::lean_inc(v___x_1003_);
        return v___x_1003_;
    }
}
pub unsafe fn l_Lean_FileMap_lineStart___boxed(
    mut v_map_1004_: *mut crate::leanh::LeanObject,
    mut v_line_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Lean_FileMap_lineStart(v_map_1004_, v_line_1005_);
    crate::leanh::lean_dec(v_line_1005_);
    crate::leanh::lean_dec_ref(v_map_1004_);
    return v_res_1006_;
}
pub unsafe fn l_String_toFileMap(
    mut v_s_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = l_Lean_FileMap_ofString(v_s_1007_);
    return v___x_1008_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Position(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Position_instToExpr = _init_l_Lean_Position_instToExpr();
    crate::leanh::lean_mark_persistent(l_Lean_Position_instToExpr);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Position(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Position(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Position(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Position(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Position(builtin);
}
