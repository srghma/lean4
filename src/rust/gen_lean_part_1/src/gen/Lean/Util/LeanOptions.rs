// Lean compiler output
// Module: Lean.Util.LeanOptions
// Imports: Lean.Data.Json.FromToJson.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_uget_borrowed, lean_int_dec_lt, lean_nat_abs, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_to_int,
    lean_string_append, lean_string_length, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen, l_String_quote,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_JsonNumber_fromNat;
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, l_Lean_NameMap_fromJson_x3f___redArg,
    l_Lean_NameMap_toJson___redArg, runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isPrefixOf,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
pub static l_Lean_instInhabitedLeanOptionValue_default___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_instInhabitedLeanOptionValue_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedLeanOptionValue_default___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedLeanOptionValue_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOptionValue_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__0_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        76, 101, 97, 110, 46, 76, 101, 97, 110, 79, 112, 116, 105, 111, 110, 86, 97, 108, 117, 101,
        46, 111, 102, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_instReprLeanOptionValue_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLeanOptionValue_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLeanOptionValue_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOptionValue_repr___closed__5_value: leanh::LeanStringObject<
    28,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        76, 101, 97, 110, 46, 76, 101, 97, 110, 79, 112, 116, 105, 111, 110, 86, 97, 108, 117, 101,
        46, 111, 102, 66, 111, 111, 108, 0,
    ],
};
static mut l_Lean_instReprLeanOptionValue_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__8_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 76, 101, 97, 110, 79, 112, 116, 105, 111, 110, 86, 97, 108, 117, 101,
        46, 111, 102, 78, 97, 116, 0,
    ],
};
static mut l_Lean_instReprLeanOptionValue_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__9_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLeanOptionValue_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instValueLeanOptionValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LeanOptionValue_toDataValue as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instValueLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instValueLeanOptionValue___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LeanOptionValue_ofDataValue_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instValueLeanOptionValue___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instValueLeanOptionValue___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instValueLeanOptionValue___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instValueLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeStringLeanOptionValue___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_instCoeStringLeanOptionValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instCoeStringLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeStringLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeBoolLeanOptionValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeBoolLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeBoolLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeNatLeanOptionValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeNatLeanOptionValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeNatLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeNatLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 76, 101, 97, 110, 79, 112, 116, 105, 111, 110, 86,
        97, 108, 117, 101, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonLeanOptionValue___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_instFromJsonLeanOptionValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonLeanOptionValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonLeanOptionValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonLeanOptionValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonLeanOptionValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptionValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LeanOptionValue_asCliFlagValue___closed__0_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [34, 0],
};
static mut l_Lean_LeanOptionValue_asCliFlagValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOptionValue_asCliFlagValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LeanOptionValue_asCliFlagValue___closed__1_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_LeanOptionValue_asCliFlagValue___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOptionValue_asCliFlagValue___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LeanOptionValue_asCliFlagValue___closed__2_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_LeanOptionValue_asCliFlagValue___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOptionValue_asCliFlagValue___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedLeanOption_default___closed__0_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedLeanOption_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOption_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOption_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOption_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOption_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__1_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__2_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__5_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__6_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLeanOption_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOption_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__10_value:
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
    m_data: [118, 97, 108, 117, 101, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLeanOption_repr___redArg___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOption_repr___redArg___closed__13_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLeanOption_repr___redArg___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLeanOption_repr___redArg___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOption_repr___redArg___closed__16_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOption___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLeanOption_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLeanOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprLeanOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LeanOption_asCliArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [45, 68, 0],
    };
static mut l_Lean_LeanOption_asCliArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOption_asCliArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_LeanOption_asCliArg___closed__1_value: leanh::LeanStringObject<2> =
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
        m_data: [61, 0],
    };
static mut l_Lean_LeanOption_asCliArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOption_asCliArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOptions_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLeanOptions: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__9_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value:
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
    m_data: [91, 93, 0],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1_value:
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
        l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value:
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
    m_data: [91, 0],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value:
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
    m_data: [93, 0],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value
) as *mut leanh::LeanObject;
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6_value:
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
        l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7_value:
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
        l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__0_value:
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
    m_data: [118, 97, 108, 117, 101, 115, 0],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__5_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        83, 116, 100, 46, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32, 0,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLeanOptions___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLeanOptions_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLeanOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprLeanOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instEmptyCollectionLeanOptions: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instAppendLeanOptions___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LeanOptions_append as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instAppendLeanOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instAppendLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instAppendLeanOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instAppendLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_LeanOptions_appendArray___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instHAppendLeanOptionsArrayLeanOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value
        ) as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonLeanOptions___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instFromJsonLeanOptions___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instFromJsonLeanOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonLeanOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonLeanOptions___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instToJsonLeanOptions___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_instToJsonLeanOptionValue___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToJsonLeanOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonLeanOptions: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_LeanOptionValue_ctorIdx(
    mut v_x_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1083_) {
        0 => {
            let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1084_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1084_;
        }
        1 => {
            let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1085_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1085_;
        }
        _ => {
            let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1086_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1086_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_ctorIdx___boxed(
    mut v_x_1087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_Lean_LeanOptionValue_ctorIdx(v_x_1087_);
    leanh::lean_dec_ref(v_x_1087_);
    return v_res_1088_;
}
pub unsafe fn l_Lean_LeanOptionValue_ctorElim___redArg(
    mut v_t_1089_: *mut leanh::LeanObject,
    mut v_k_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1089_) {
        0 => {
            let mut v_s_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_s_1091_ = leanh::lean_ctor_get(v_t_1089_, 0);
            leanh::lean_inc_ref(v_s_1091_);
            leanh::lean_dec_ref_known(v_t_1089_, 1);
            v___x_1092_ = leanh::lean_apply_1(v_k_1090_, v_s_1091_);
            return v___x_1092_;
        }
        1 => {
            let mut v_b_1093_: u8 = 0;
            let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_b_1093_ = leanh::lean_ctor_get_uint8(v_t_1089_, 0 as u32);
            leanh::lean_dec_ref_known(v_t_1089_, 0);
            v___x_1094_ = leanh::lean_box((v_b_1093_) as usize);
            v___x_1095_ = leanh::lean_apply_1(v_k_1090_, v___x_1094_);
            return v___x_1095_;
        }
        _ => {
            let mut v_n_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_1096_ = leanh::lean_ctor_get(v_t_1089_, 0);
            leanh::lean_inc(v_n_1096_);
            leanh::lean_dec_ref_known(v_t_1089_, 1);
            v___x_1097_ = leanh::lean_apply_1(v_k_1090_, v_n_1096_);
            return v___x_1097_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_ctorElim(
    mut v_motive_1098_: *mut leanh::LeanObject,
    mut v_ctorIdx_1099_: *mut leanh::LeanObject,
    mut v_t_1100_: *mut leanh::LeanObject,
    mut v_h_1101_: *mut leanh::LeanObject,
    mut v_k_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1103_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1100_, v_k_1102_);
    return v___x_1103_;
}
pub unsafe fn l_Lean_LeanOptionValue_ctorElim___boxed(
    mut v_motive_1104_: *mut leanh::LeanObject,
    mut v_ctorIdx_1105_: *mut leanh::LeanObject,
    mut v_t_1106_: *mut leanh::LeanObject,
    mut v_h_1107_: *mut leanh::LeanObject,
    mut v_k_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_LeanOptionValue_ctorElim(
        v_motive_1104_,
        v_ctorIdx_1105_,
        v_t_1106_,
        v_h_1107_,
        v_k_1108_,
    );
    leanh::lean_dec(v_ctorIdx_1105_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofString_elim___redArg(
    mut v_t_1110_: *mut leanh::LeanObject,
    mut v_ofString_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1110_, v_ofString_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofString_elim(
    mut v_motive_1113_: *mut leanh::LeanObject,
    mut v_t_1114_: *mut leanh::LeanObject,
    mut v_h_1115_: *mut leanh::LeanObject,
    mut v_ofString_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1114_, v_ofString_1116_);
    return v___x_1117_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofBool_elim___redArg(
    mut v_t_1118_: *mut leanh::LeanObject,
    mut v_ofBool_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1118_, v_ofBool_1119_);
    return v___x_1120_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofBool_elim(
    mut v_motive_1121_: *mut leanh::LeanObject,
    mut v_t_1122_: *mut leanh::LeanObject,
    mut v_h_1123_: *mut leanh::LeanObject,
    mut v_ofBool_1124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1122_, v_ofBool_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofNat_elim___redArg(
    mut v_t_1126_: *mut leanh::LeanObject,
    mut v_ofNat_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1126_, v_ofNat_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofNat_elim(
    mut v_motive_1129_: *mut leanh::LeanObject,
    mut v_t_1130_: *mut leanh::LeanObject,
    mut v_h_1131_: *mut leanh::LeanObject,
    mut v_ofNat_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1130_, v_ofNat_1132_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lean_instReprLeanOptionValue_repr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = leanh::lean_unsigned_to_nat(2);
    v___x_1146_ = lean_nat_to_int(v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn _init_l_Lean_instReprLeanOptionValue_repr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = leanh::lean_unsigned_to_nat(1);
    v___x_1148_ = lean_nat_to_int(v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_instReprLeanOptionValue_repr(
    mut v_x_1161_: *mut leanh::LeanObject,
    mut v_prec_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___y_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1183_: u8 = 0;
    let mut v_b_1184_: u8 = 0;
    let mut v___y_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___y_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1161_) {
                0 => {
                    v_s_1163_ = leanh::lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1183_ = (!leanh::lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1183_ == 0 {
                        v___x_1165_ = v_x_1161_;
                        v_isShared_1166_ = v_isSharedCheck_1183_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1163_);
                        leanh::lean_dec(v_x_1161_);
                        v___x_1165_ = leanh::lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1183_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_b_1184_ = leanh::lean_ctor_get_uint8(v_x_1161_, 0 as u32);
                    leanh::lean_dec_ref_known(v_x_1161_, 0);
                    v___x_1194_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1195_ = lean_nat_dec_le(v___x_1194_, v_prec_1162_);
                    if v___x_1195_ == 0 {
                        v___x_1196_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprLeanOptionValue_repr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprLeanOptionValue_repr___closed__3_once
                            ),
                            _init_l_Lean_instReprLeanOptionValue_repr___closed__3,
                        );
                        v___y_1186_ = v___x_1196_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1197_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprLeanOptionValue_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprLeanOptionValue_repr___closed__4_once
                            ),
                            _init_l_Lean_instReprLeanOptionValue_repr___closed__4,
                        );
                        v___y_1186_ = v___x_1197_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v_n_1198_ = leanh::lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1218_ = (!leanh::lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1218_ == 0 {
                        v___x_1200_ = v_x_1161_;
                        v_isShared_1201_ = v_isSharedCheck_1218_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_1198_);
                        leanh::lean_dec(v_x_1161_);
                        v___x_1200_ = leanh::lean_box(0);
                        v_isShared_1201_ = v_isSharedCheck_1218_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1179_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1180_ = lean_nat_dec_le(v___x_1179_, v_prec_1162_);
                if v___x_1180_ == 0 {
                    v___x_1181_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptionValue_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_instReprLeanOptionValue_repr___closed__3_once
                        ),
                        _init_l_Lean_instReprLeanOptionValue_repr___closed__3,
                    );
                    v___y_1168_ = v___x_1181_;
                    state = 2;
                    continue;
                } else {
                    v___x_1182_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptionValue_repr___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_instReprLeanOptionValue_repr___closed__4_once
                        ),
                        _init_l_Lean_instReprLeanOptionValue_repr___closed__4,
                    );
                    v___y_1168_ = v___x_1182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1169_ = l_Lean_instReprLeanOptionValue_repr___closed__2;
                v___x_1170_ = l_String_quote(v_s_1163_);
                if v_isShared_1166_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1165_, 3);
                    leanh::lean_ctor_set(v___x_1165_, 0, v___x_1170_);
                    v___x_1172_ = v___x_1165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1170_);
                    v___x_1172_ = v_reuseFailAlloc_1178_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1173_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1173_, 0, v___x_1169_);
                leanh::lean_ctor_set(v___x_1173_, 1, v___x_1172_);
                leanh::lean_inc(v___y_1168_);
                v___x_1174_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1174_, 0, v___y_1168_);
                leanh::lean_ctor_set(v___x_1174_, 1, v___x_1173_);
                v___x_1175_ = 0;
                v___x_1176_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1176_, 0, v___x_1174_);
                leanh::lean_ctor_set_uint8(
                    v___x_1176_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1175_,
                );
                v___x_1177_ = l_Repr_addAppParen(v___x_1176_, v_prec_1162_);
                return v___x_1177_;
            }
            4 => {
                v___x_1187_ = l_Lean_instReprLeanOptionValue_repr___closed__7;
                v___x_1188_ = l_Bool_repr___redArg(v_b_1184_);
                v___x_1189_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1189_, 0, v___x_1187_);
                leanh::lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                leanh::lean_inc(v___y_1186_);
                v___x_1190_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1190_, 0, v___y_1186_);
                leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                v___x_1191_ = 0;
                v___x_1192_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1192_, 0, v___x_1190_);
                leanh::lean_ctor_set_uint8(
                    v___x_1192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1191_,
                );
                v___x_1193_ = l_Repr_addAppParen(v___x_1192_, v_prec_1162_);
                return v___x_1193_;
            }
            5 => {
                v___x_1214_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1215_ = lean_nat_dec_le(v___x_1214_, v_prec_1162_);
                if v___x_1215_ == 0 {
                    v___x_1216_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptionValue_repr___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_instReprLeanOptionValue_repr___closed__3_once
                        ),
                        _init_l_Lean_instReprLeanOptionValue_repr___closed__3,
                    );
                    v___y_1203_ = v___x_1216_;
                    state = 6;
                    continue;
                } else {
                    v___x_1217_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptionValue_repr___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Lean_instReprLeanOptionValue_repr___closed__4_once
                        ),
                        _init_l_Lean_instReprLeanOptionValue_repr___closed__4,
                    );
                    v___y_1203_ = v___x_1217_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1204_ = l_Lean_instReprLeanOptionValue_repr___closed__10;
                v___x_1205_ = l_Nat_reprFast(v_n_1198_);
                if v_isShared_1201_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1200_, 3);
                    leanh::lean_ctor_set(v___x_1200_, 0, v___x_1205_);
                    v___x_1207_ = v___x_1200_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1205_);
                    v___x_1207_ = v_reuseFailAlloc_1213_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1208_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1208_, 0, v___x_1204_);
                leanh::lean_ctor_set(v___x_1208_, 1, v___x_1207_);
                leanh::lean_inc(v___y_1203_);
                v___x_1209_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1209_, 0, v___y_1203_);
                leanh::lean_ctor_set(v___x_1209_, 1, v___x_1208_);
                v___x_1210_ = 0;
                v___x_1211_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1211_, 0, v___x_1209_);
                leanh::lean_ctor_set_uint8(
                    v___x_1211_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1210_,
                );
                v___x_1212_ = l_Repr_addAppParen(v___x_1211_, v_prec_1162_);
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprLeanOptionValue_repr___boxed(
    mut v_x_1219_: *mut leanh::LeanObject,
    mut v_prec_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_instReprLeanOptionValue_repr(v_x_1219_, v_prec_1220_);
    leanh::lean_dec(v_prec_1220_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofDataValue_x3f(
    mut v_x_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1228_: u8 = 0;
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut v_v_1234_: u8 = 0;
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1242_: u8 = 0;
    let mut v_v_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1224_) {
                0 => {
                    v_v_1225_ = leanh::lean_ctor_get(v_x_1224_, 0);
                    v_isSharedCheck_1233_ = (!leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1227_ = v_x_1224_;
                        v_isShared_1228_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1225_);
                        leanh::lean_dec(v_x_1224_);
                        v___x_1227_ = leanh::lean_box(0);
                        v_isShared_1228_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_v_1234_ = leanh::lean_ctor_get_uint8(v_x_1224_, 0 as u32);
                    v_isSharedCheck_1242_ = (!leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1242_ == 0 {
                        v___x_1236_ = v_x_1224_;
                        v_isShared_1237_ = v_isSharedCheck_1242_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1224_);
                        v___x_1236_ = leanh::lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1242_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_v_1243_ = leanh::lean_ctor_get(v_x_1224_, 0);
                    v_isSharedCheck_1251_ = (!leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v___x_1245_ = v_x_1224_;
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1243_);
                        leanh::lean_dec(v_x_1224_);
                        v___x_1245_ = leanh::lean_box(0);
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_x_1224_);
                    v___x_1252_ = leanh::lean_box(0);
                    return v___x_1252_;
                }
            },
            1 => {
                if v_isShared_1228_ == 0 {
                    v___x_1230_ = v___x_1227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_v_1225_);
                    v___x_1230_ = v_reuseFailAlloc_1232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1231_, 0, v___x_1230_);
                return v___x_1231_;
            }
            3 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1241_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1241_, 0 as u32, v_v_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1240_, 0, v___x_1239_);
                return v___x_1240_;
            }
            5 => {
                if v_isShared_1246_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1245_, 2);
                    v___x_1248_ = v___x_1245_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_v_1243_);
                    v___x_1248_ = v_reuseFailAlloc_1250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1249_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1249_, 0, v___x_1248_);
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_toDataValue(
    mut v_x_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_b_1262_: u8 = 0;
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1269_: u8 = 0;
    let mut v_n_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1273_: u8 = 0;
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1253_) {
                0 => {
                    v_s_1254_ = leanh::lean_ctor_get(v_x_1253_, 0);
                    v_isSharedCheck_1261_ = (!leanh::lean_is_exclusive(v_x_1253_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1256_ = v_x_1253_;
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1254_);
                        leanh::lean_dec(v_x_1253_);
                        v___x_1256_ = leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_b_1262_ = leanh::lean_ctor_get_uint8(v_x_1253_, 0 as u32);
                    v_isSharedCheck_1269_ = (!leanh::lean_is_exclusive(v_x_1253_)) as u8;
                    if v_isSharedCheck_1269_ == 0 {
                        v___x_1264_ = v_x_1253_;
                        v_isShared_1265_ = v_isSharedCheck_1269_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1253_);
                        v___x_1264_ = leanh::lean_box(0);
                        v_isShared_1265_ = v_isSharedCheck_1269_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_n_1270_ = leanh::lean_ctor_get(v_x_1253_, 0);
                    v_isSharedCheck_1277_ = (!leanh::lean_is_exclusive(v_x_1253_)) as u8;
                    if v_isSharedCheck_1277_ == 0 {
                        v___x_1272_ = v_x_1253_;
                        v_isShared_1273_ = v_isSharedCheck_1277_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_1270_);
                        leanh::lean_dec(v_x_1253_);
                        v___x_1272_ = leanh::lean_box(0);
                        v_isShared_1273_ = v_isSharedCheck_1277_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_1257_ == 0 {
                    v___x_1259_ = v___x_1256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_s_1254_);
                    v___x_1259_ = v_reuseFailAlloc_1260_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1259_;
            }
            3 => {
                if v_isShared_1265_ == 0 {
                    v___x_1267_ = v___x_1264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1268_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1268_, 0 as u32, v_b_1262_);
                    v___x_1267_ = v_reuseFailAlloc_1268_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1267_;
            }
            5 => {
                if v_isShared_1273_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1272_, 3);
                    v___x_1275_ = v___x_1272_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_n_1270_);
                    v___x_1275_ = v_reuseFailAlloc_1276_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instCoeStringLeanOptionValue___lam__0(
    mut v_s_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1285_, 0, v_s_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_instCoeBoolLeanOptionValue___lam__0(
    mut v_b_1288_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_1289_, 0 as u32, v_b_1288_);
    return v___x_1289_;
}
pub unsafe fn l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed(
    mut v_b_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1291_: u8 = 0;
    let mut v_res_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1291_ = (leanh::lean_unbox(v_b_1290_) as u8);
    v_res_1292_ = l_Lean_instCoeBoolLeanOptionValue___lam__0(v_b_boxed_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_instCoeNatLeanOptionValue___lam__0(
    mut v_n_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1296_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1296_, 0, v_n_1295_);
    return v___x_1296_;
}
pub unsafe fn l_Lean_instOfNatLeanOptionValue(
    mut v_n_1299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1300_, 0, v_n_1299_);
    return v___x_1300_;
}
pub unsafe fn _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v_natZero_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_1304_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_1305_ = lean_nat_to_int(v_natZero_1304_);
    return v_intZero_1305_;
}
pub unsafe fn l_Lean_instFromJsonLeanOptionValue___lam__0(
    mut v_x_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1317_: u8 = 0;
    let mut v_b_1318_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_n_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v_mantissa_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1335_: u8 = 0;
    let mut v___x_1336_: u8 = 0;
    let mut v_a_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1306_) {
                3 => {
                    v_s_1309_ = leanh::lean_ctor_get(v_x_1306_, 0);
                    v_isSharedCheck_1317_ = (!leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1317_ == 0 {
                        v___x_1311_ = v_x_1306_;
                        v_isShared_1312_ = v_isSharedCheck_1317_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1309_);
                        leanh::lean_dec(v_x_1306_);
                        v___x_1311_ = leanh::lean_box(0);
                        v_isShared_1312_ = v_isSharedCheck_1317_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_b_1318_ = leanh::lean_ctor_get_uint8(v_x_1306_, 0 as u32);
                    v_isSharedCheck_1326_ = (!leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1320_ = v_x_1306_;
                        v_isShared_1321_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1306_);
                        v___x_1320_ = leanh::lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_n_1327_ = leanh::lean_ctor_get(v_x_1306_, 0);
                    v_isSharedCheck_1342_ = (!leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v___x_1329_ = v_x_1306_;
                        v_isShared_1330_ = v_isSharedCheck_1342_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_1327_);
                        leanh::lean_dec(v_x_1306_);
                        v___x_1329_ = leanh::lean_box(0);
                        v_isShared_1330_ = v_isSharedCheck_1342_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_1306_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1308_ = l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1;
                return v___x_1308_;
            }
            2 => {
                if v_isShared_1312_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1311_, 0);
                    v___x_1314_ = v___x_1311_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1316_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_s_1309_);
                    v___x_1314_ = v_reuseFailAlloc_1316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1315_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1315_, 0, v___x_1314_);
                return v___x_1315_;
            }
            4 => {
                if v_isShared_1321_ == 0 {
                    v___x_1323_ = v___x_1320_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 0 as u32, v_b_1318_);
                    v___x_1323_ = v_reuseFailAlloc_1325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                return v___x_1324_;
            }
            6 => {
                v_mantissa_1331_ = leanh::lean_ctor_get(v_n_1327_, 0);
                leanh::lean_inc(v_mantissa_1331_);
                v_exponent_1332_ = leanh::lean_ctor_get(v_n_1327_, 1);
                leanh::lean_inc(v_exponent_1332_);
                leanh::lean_dec_ref(v_n_1327_);
                v_natZero_1333_ = leanh::lean_unsigned_to_nat(0);
                v_intZero_1334_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2_once
                    ),
                    _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2,
                );
                v_isNeg_1335_ = lean_int_dec_lt(v_mantissa_1331_, v_intZero_1334_);
                if v_isNeg_1335_ == 0 {
                    v___x_1336_ = lean_nat_dec_eq(v_exponent_1332_, v_natZero_1333_);
                    leanh::lean_dec(v_exponent_1332_);
                    if v___x_1336_ == 0 {
                        leanh::lean_dec(v_mantissa_1331_);
                        leanh::lean_del_object(v___x_1329_);
                        state = 1;
                        continue;
                    } else {
                        v_a_1337_ = lean_nat_abs(v_mantissa_1331_);
                        leanh::lean_dec(v_mantissa_1331_);
                        if v_isShared_1330_ == 0 {
                            leanh::lean_ctor_set(v___x_1329_, 0, v_a_1337_);
                            v___x_1339_ = v___x_1329_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1341_ =
                                leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1337_);
                            v___x_1339_ = v_reuseFailAlloc_1341_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_exponent_1332_);
                    leanh::lean_dec(v_mantissa_1331_);
                    leanh::lean_del_object(v___x_1329_);
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_1340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1340_, 0, v___x_1339_);
                return v___x_1340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonLeanOptionValue___lam__0(
    mut v_x_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_b_1354_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_n_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1365_: u8 = 0;
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1345_) {
                0 => {
                    v_s_1346_ = leanh::lean_ctor_get(v_x_1345_, 0);
                    v_isSharedCheck_1353_ = (!leanh::lean_is_exclusive(v_x_1345_)) as u8;
                    if v_isSharedCheck_1353_ == 0 {
                        v___x_1348_ = v_x_1345_;
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1346_);
                        leanh::lean_dec(v_x_1345_);
                        v___x_1348_ = leanh::lean_box(0);
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_b_1354_ = leanh::lean_ctor_get_uint8(v_x_1345_, 0 as u32);
                    v_isSharedCheck_1361_ = (!leanh::lean_is_exclusive(v_x_1345_)) as u8;
                    if v_isSharedCheck_1361_ == 0 {
                        v___x_1356_ = v_x_1345_;
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1345_);
                        v___x_1356_ = leanh::lean_box(0);
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_n_1362_ = leanh::lean_ctor_get(v_x_1345_, 0);
                    v_isSharedCheck_1370_ = (!leanh::lean_is_exclusive(v_x_1345_)) as u8;
                    if v_isSharedCheck_1370_ == 0 {
                        v___x_1364_ = v_x_1345_;
                        v_isShared_1365_ = v_isSharedCheck_1370_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_1362_);
                        leanh::lean_dec(v_x_1345_);
                        v___x_1364_ = leanh::lean_box(0);
                        v_isShared_1365_ = v_isSharedCheck_1370_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_1349_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1348_, 3);
                    v___x_1351_ = v___x_1348_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_s_1346_);
                    v___x_1351_ = v_reuseFailAlloc_1352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1351_;
            }
            3 => {
                if v_isShared_1357_ == 0 {
                    v___x_1359_ = v___x_1356_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 0 as u32, v_b_1354_);
                    v___x_1359_ = v_reuseFailAlloc_1360_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1359_;
            }
            5 => {
                v___x_1366_ = l_Lean_JsonNumber_fromNat(v_n_1362_);
                if v_isShared_1365_ == 0 {
                    leanh::lean_ctor_set(v___x_1364_, 0, v___x_1366_);
                    v___x_1368_ = v___x_1364_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
                    v___x_1368_ = v_reuseFailAlloc_1369_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_asCliFlagValue(
    mut v_x_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1376_) {
        0 => {
            let mut v_s_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_s_1377_ = leanh::lean_ctor_get(v_x_1376_, 0);
            leanh::lean_inc_ref(v_s_1377_);
            leanh::lean_dec_ref_known(v_x_1376_, 1);
            v___x_1378_ = l_Lean_LeanOptionValue_asCliFlagValue___closed__0;
            v___x_1379_ = lean_string_append(v___x_1378_, v_s_1377_);
            leanh::lean_dec_ref(v_s_1377_);
            v___x_1380_ = lean_string_append(v___x_1379_, v___x_1378_);
            return v___x_1380_;
        }
        1 => {
            let mut v_b_1381_: u8 = 0;
            v_b_1381_ = leanh::lean_ctor_get_uint8(v_x_1376_, 0 as u32);
            leanh::lean_dec_ref_known(v_x_1376_, 0);
            if v_b_1381_ == 0 {
                let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1382_ = l_Lean_LeanOptionValue_asCliFlagValue___closed__1;
                return v___x_1382_;
            } else {
                let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1383_ = l_Lean_LeanOptionValue_asCliFlagValue___closed__2;
                return v___x_1383_;
            }
        }
        _ => {
            let mut v_n_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_1384_ = leanh::lean_ctor_get(v_x_1376_, 0);
            leanh::lean_inc(v_n_1384_);
            leanh::lean_dec_ref_known(v_x_1376_, 1);
            v___x_1385_ = l_Nat_reprFast(v_n_1384_);
            return v___x_1385_;
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprLeanOption_repr_spec__0(
    mut v_a_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = lean_nat_to_int(v_a_1391_);
    return v___x_1392_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = leanh::lean_unsigned_to_nat(8);
    v___x_1407_ = lean_nat_to_int(v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = leanh::lean_unsigned_to_nat(9);
    v___x_1415_ = lean_nat_to_int(v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_instReprLeanOption_repr___redArg___closed__0;
    v___x_1418_ = lean_string_length(v___x_1417_);
    return v___x_1418_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__14_once),
        _init_l_Lean_instReprLeanOption_repr___redArg___closed__14,
    );
    v___x_1420_ = lean_nat_to_int(v___x_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Lean_instReprLeanOption_repr___redArg(
    mut v_x_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1426_ = leanh::lean_ctor_get(v_x_1425_, 0);
                v_value_1427_ = leanh::lean_ctor_get(v_x_1425_, 1);
                v_isSharedCheck_1461_ = (!leanh::lean_is_exclusive(v_x_1425_)) as u8;
                if v_isSharedCheck_1461_ == 0 {
                    v___x_1429_ = v_x_1425_;
                    v_isShared_1430_ = v_isSharedCheck_1461_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_value_1427_);
                    leanh::lean_inc(v_name_1426_);
                    leanh::lean_dec(v_x_1425_);
                    v___x_1429_ = leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1461_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1431_ = l_Lean_instReprLeanOption_repr___redArg___closed__5;
                v___x_1432_ = l_Lean_instReprLeanOption_repr___redArg___closed__6;
                v___x_1433_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprLeanOption_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_instReprLeanOption_repr___redArg___closed__7,
                );
                v___x_1434_ = leanh::lean_unsigned_to_nat(0);
                v___x_1435_ = l_Lean_Name_reprPrec(v_name_1426_, v___x_1434_);
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1429_, 4);
                    leanh::lean_ctor_set(v___x_1429_, 1, v___x_1435_);
                    leanh::lean_ctor_set(v___x_1429_, 0, v___x_1433_);
                    v___x_1437_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1460_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1435_);
                    v___x_1437_ = v_reuseFailAlloc_1460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1438_ = 0;
                v___x_1439_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1439_, 0, v___x_1437_);
                leanh::lean_ctor_set_uint8(
                    v___x_1439_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1438_,
                );
                v___x_1440_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1440_, 0, v___x_1432_);
                leanh::lean_ctor_set(v___x_1440_, 1, v___x_1439_);
                v___x_1441_ = l_Lean_instReprLeanOption_repr___redArg___closed__9;
                v___x_1442_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1442_, 0, v___x_1440_);
                leanh::lean_ctor_set(v___x_1442_, 1, v___x_1441_);
                v___x_1443_ = leanh::lean_box(1);
                v___x_1444_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1444_, 0, v___x_1442_);
                leanh::lean_ctor_set(v___x_1444_, 1, v___x_1443_);
                v___x_1445_ = l_Lean_instReprLeanOption_repr___redArg___closed__11;
                v___x_1446_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1446_, 0, v___x_1444_);
                leanh::lean_ctor_set(v___x_1446_, 1, v___x_1445_);
                v___x_1447_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1447_, 0, v___x_1446_);
                leanh::lean_ctor_set(v___x_1447_, 1, v___x_1431_);
                v___x_1448_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprLeanOption_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_instReprLeanOption_repr___redArg___closed__12,
                );
                v___x_1449_ = l_Lean_instReprLeanOptionValue_repr(v_value_1427_, v___x_1434_);
                v___x_1450_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1450_, 0, v___x_1448_);
                leanh::lean_ctor_set(v___x_1450_, 1, v___x_1449_);
                v___x_1451_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                leanh::lean_ctor_set_uint8(
                    v___x_1451_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1438_,
                );
                v___x_1452_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1452_, 0, v___x_1447_);
                leanh::lean_ctor_set(v___x_1452_, 1, v___x_1451_);
                v___x_1453_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprLeanOption_repr___redArg___closed__15_once
                    ),
                    _init_l_Lean_instReprLeanOption_repr___redArg___closed__15,
                );
                v___x_1454_ = l_Lean_instReprLeanOption_repr___redArg___closed__16;
                v___x_1455_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1455_, 0, v___x_1454_);
                leanh::lean_ctor_set(v___x_1455_, 1, v___x_1452_);
                v___x_1456_ = l_Lean_instReprLeanOption_repr___redArg___closed__17;
                v___x_1457_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1457_, 0, v___x_1455_);
                leanh::lean_ctor_set(v___x_1457_, 1, v___x_1456_);
                v___x_1458_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1458_, 0, v___x_1453_);
                leanh::lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                v___x_1459_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1459_, 0, v___x_1458_);
                leanh::lean_ctor_set_uint8(
                    v___x_1459_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1438_,
                );
                return v___x_1459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprLeanOption_repr(
    mut v_x_1462_: *mut leanh::LeanObject,
    mut v_prec_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = l_Lean_instReprLeanOption_repr___redArg(v_x_1462_);
    return v___x_1464_;
}
pub unsafe fn l_Lean_instReprLeanOption_repr___boxed(
    mut v_x_1465_: *mut leanh::LeanObject,
    mut v_prec_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Lean_instReprLeanOption_repr(v_x_1465_, v_prec_1466_);
    leanh::lean_dec(v_prec_1466_);
    return v_res_1467_;
}
pub unsafe fn l_Lean_LeanOption_asCliArg(
    mut v_o_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1473_ = leanh::lean_ctor_get(v_o_1472_, 0);
    leanh::lean_inc(v_name_1473_);
    v_value_1474_ = leanh::lean_ctor_get(v_o_1472_, 1);
    leanh::lean_inc_ref(v_value_1474_);
    leanh::lean_dec_ref(v_o_1472_);
    v___x_1475_ = l_Lean_LeanOption_asCliArg___closed__0;
    v___x_1476_ = 1;
    v___x_1477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1473_,
        v___x_1476_,
    );
    v___x_1478_ = lean_string_append(v___x_1475_, v___x_1477_);
    leanh::lean_dec_ref(v___x_1477_);
    v___x_1479_ = l_Lean_LeanOption_asCliArg___closed__1;
    v___x_1480_ = lean_string_append(v___x_1478_, v___x_1479_);
    v___x_1481_ = l_Lean_LeanOptionValue_asCliFlagValue(v_value_1474_);
    v___x_1482_ = lean_string_append(v___x_1480_, v___x_1481_);
    leanh::lean_dec_ref(v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lean_instInhabitedLeanOptions_default() -> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = leanh::lean_box(1);
    return v___x_1483_;
}
pub unsafe fn _init_l_Lean_instInhabitedLeanOptions() -> *mut leanh::LeanObject {
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = leanh::lean_box(1);
    return v___x_1484_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(
    mut v_x_1485_: *mut leanh::LeanObject,
    mut v_x_1486_: *mut leanh::LeanObject,
    mut v_x_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1487_) == 0 {
                    leanh::lean_dec(v_x_1485_);
                    return v_x_1486_;
                } else {
                    v_head_1488_ = leanh::lean_ctor_get(v_x_1487_, 0);
                    v_tail_1489_ = leanh::lean_ctor_get(v_x_1487_, 1);
                    v_isSharedCheck_1498_ = (!leanh::lean_is_exclusive(v_x_1487_)) as u8;
                    if v_isSharedCheck_1498_ == 0 {
                        v___x_1491_ = v_x_1487_;
                        v_isShared_1492_ = v_isSharedCheck_1498_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1489_);
                        leanh::lean_inc(v_head_1488_);
                        leanh::lean_dec(v_x_1487_);
                        v___x_1491_ = leanh::lean_box(0);
                        v_isShared_1492_ = v_isSharedCheck_1498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1485_);
                if v_isShared_1492_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1491_, 5);
                    leanh::lean_ctor_set(v___x_1491_, 1, v_x_1485_);
                    leanh::lean_ctor_set(v___x_1491_, 0, v_x_1486_);
                    v___x_1494_ = v___x_1491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_x_1486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_x_1485_);
                    v___x_1494_ = v_reuseFailAlloc_1497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1495_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                leanh::lean_ctor_set(v___x_1495_, 1, v_head_1488_);
                v_x_1486_ = v___x_1495_;
                v_x_1487_ = v_tail_1489_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(
    mut v_x_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1499_) == 0 {
        let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1500_);
        v___x_1501_ = leanh::lean_box(0);
        return v___x_1501_;
    } else {
        let mut v_tail_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1502_ = leanh::lean_ctor_get(v_x_1499_, 1);
        if leanh::lean_obj_tag(v_tail_1502_) == 0 {
            let mut v_head_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1500_);
            v_head_1503_ = leanh::lean_ctor_get(v_x_1499_, 0);
            leanh::lean_inc(v_head_1503_);
            leanh::lean_dec_ref_known(v_x_1499_, 2);
            return v_head_1503_;
        } else {
            let mut v_head_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1502_);
            v_head_1504_ = leanh::lean_ctor_get(v_x_1499_, 0);
            leanh::lean_inc(v_head_1504_);
            leanh::lean_dec_ref_known(v_x_1499_, 2);
            v___x_1505_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(v_x_1500_, v_head_1504_, v_tail_1502_);
            return v___x_1505_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0;
    v___x_1512_ = lean_string_length(v___x_1511_);
    return v___x_1512_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3);
    v___x_1514_ = lean_nat_to_int(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(
    mut v_x_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1520_ = leanh::lean_ctor_get(v_x_1519_, 0);
                v_snd_1521_ = leanh::lean_ctor_get(v_x_1519_, 1);
                v_isSharedCheck_1544_ = (!leanh::lean_is_exclusive(v_x_1519_)) as u8;
                if v_isSharedCheck_1544_ == 0 {
                    v___x_1523_ = v_x_1519_;
                    v_isShared_1524_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1521_);
                    leanh::lean_inc(v_fst_1520_);
                    leanh::lean_dec(v_x_1519_);
                    v___x_1523_ = leanh::lean_box(0);
                    v_isShared_1524_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1525_ = leanh::lean_unsigned_to_nat(0);
                v___x_1526_ = l_Lean_Name_reprPrec(v_fst_1520_, v___x_1525_);
                v___x_1527_ = leanh::lean_box(0);
                if v_isShared_1524_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1523_, 1);
                    leanh::lean_ctor_set(v___x_1523_, 1, v___x_1527_);
                    leanh::lean_ctor_set(v___x_1523_, 0, v___x_1526_);
                    v___x_1529_ = v___x_1523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1530_ = l_Lean_instReprLeanOptionValue_repr(v_snd_1521_, v___x_1525_);
                v___x_1531_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
                leanh::lean_ctor_set(v___x_1531_, 1, v___x_1529_);
                v___x_1532_ = l_List_reverse___redArg(v___x_1531_);
                v___x_1533_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1;
                v___x_1534_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(v___x_1532_, v___x_1533_);
                v___x_1535_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4);
                v___x_1536_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5;
                v___x_1537_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                leanh::lean_ctor_set(v___x_1537_, 1, v___x_1534_);
                v___x_1538_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6;
                v___x_1539_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1539_, 0, v___x_1537_);
                leanh::lean_ctor_set(v___x_1539_, 1, v___x_1538_);
                v___x_1540_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1540_, 0, v___x_1535_);
                leanh::lean_ctor_set(v___x_1540_, 1, v___x_1539_);
                v___x_1541_ = 0;
                v___x_1542_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1542_, 0, v___x_1540_);
                leanh::lean_ctor_set_uint8(
                    v___x_1542_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1541_,
                );
                return v___x_1542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(
    mut v_x_1545_: *mut leanh::LeanObject,
    mut v_x_1546_: *mut leanh::LeanObject,
    mut v_x_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1547_) == 0 {
                    leanh::lean_dec(v_x_1545_);
                    return v_x_1546_;
                } else {
                    v_head_1548_ = leanh::lean_ctor_get(v_x_1547_, 0);
                    v_tail_1549_ = leanh::lean_ctor_get(v_x_1547_, 1);
                    v_isSharedCheck_1559_ = (!leanh::lean_is_exclusive(v_x_1547_)) as u8;
                    if v_isSharedCheck_1559_ == 0 {
                        v___x_1551_ = v_x_1547_;
                        v_isShared_1552_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1549_);
                        leanh::lean_inc(v_head_1548_);
                        leanh::lean_dec(v_x_1547_);
                        v___x_1551_ = leanh::lean_box(0);
                        v_isShared_1552_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1545_);
                if v_isShared_1552_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1551_, 5);
                    leanh::lean_ctor_set(v___x_1551_, 1, v_x_1545_);
                    leanh::lean_ctor_set(v___x_1551_, 0, v_x_1546_);
                    v___x_1554_ = v___x_1551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_x_1546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_x_1545_);
                    v___x_1554_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1555_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1548_);
                v___x_1556_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1556_, 0, v___x_1554_);
                leanh::lean_ctor_set(v___x_1556_, 1, v___x_1555_);
                v_x_1546_ = v___x_1556_;
                v_x_1547_ = v_tail_1549_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(
    mut v_x_1560_: *mut leanh::LeanObject,
    mut v_x_1561_: *mut leanh::LeanObject,
    mut v_x_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1562_) == 0 {
                    leanh::lean_dec(v_x_1560_);
                    return v_x_1561_;
                } else {
                    v_head_1563_ = leanh::lean_ctor_get(v_x_1562_, 0);
                    v_tail_1564_ = leanh::lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1574_ = (!leanh::lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1574_ == 0 {
                        v___x_1566_ = v_x_1562_;
                        v_isShared_1567_ = v_isSharedCheck_1574_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1564_);
                        leanh::lean_inc(v_head_1563_);
                        leanh::lean_dec(v_x_1562_);
                        v___x_1566_ = leanh::lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1574_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1560_);
                if v_isShared_1567_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1566_, 5);
                    leanh::lean_ctor_set(v___x_1566_, 1, v_x_1560_);
                    leanh::lean_ctor_set(v___x_1566_, 0, v_x_1561_);
                    v___x_1569_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_x_1561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_x_1560_);
                    v___x_1569_ = v_reuseFailAlloc_1573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1570_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1563_);
                v___x_1571_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1571_, 0, v___x_1569_);
                leanh::lean_ctor_set(v___x_1571_, 1, v___x_1570_);
                v___x_1572_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(v_x_1560_, v___x_1571_, v_tail_1564_);
                return v___x_1572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(
    mut v_x_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1575_) == 0 {
        let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1576_);
        v___x_1577_ = leanh::lean_box(0);
        return v___x_1577_;
    } else {
        let mut v_tail_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1578_ = leanh::lean_ctor_get(v_x_1575_, 1);
        if leanh::lean_obj_tag(v_tail_1578_) == 0 {
            let mut v_head_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1576_);
            v_head_1579_ = leanh::lean_ctor_get(v_x_1575_, 0);
            leanh::lean_inc(v_head_1579_);
            leanh::lean_dec_ref_known(v_x_1575_, 2);
            v___x_1580_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1579_);
            return v___x_1580_;
        } else {
            let mut v_head_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1578_);
            v_head_1581_ = leanh::lean_ctor_get(v_x_1575_, 0);
            leanh::lean_inc(v_head_1581_);
            leanh::lean_dec_ref_known(v_x_1575_, 2);
            v___x_1582_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1581_);
            v___x_1583_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(v_x_1576_, v___x_1582_, v_tail_1578_);
            return v___x_1583_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2;
    v___x_1590_ = lean_string_length(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4_once
        ),
        _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4,
    );
    v___x_1592_ = lean_nat_to_int(v___x_1591_);
    return v___x_1592_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(
    mut v_a_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_1597_) == 0 {
        let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1598_ =
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1;
        return v___x_1598_;
    } else {
        let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: u8 = 0;
        let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1599_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1;
        v___x_1600_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(v_a_1597_, v___x_1599_);
        v___x_1601_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once), _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5);
        v___x_1602_ =
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6;
        v___x_1603_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1603_, 0, v___x_1602_);
        leanh::lean_ctor_set(v___x_1603_, 1, v___x_1600_);
        v___x_1604_ =
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7;
        v___x_1605_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1605_, 0, v___x_1603_);
        leanh::lean_ctor_set(v___x_1605_, 1, v___x_1604_);
        v___x_1606_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1606_, 0, v___x_1601_);
        leanh::lean_ctor_set(v___x_1606_, 1, v___x_1605_);
        v___x_1607_ = 0;
        v___x_1608_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1608_, 0, v___x_1606_);
        leanh::lean_ctor_set_uint8(
            v___x_1608_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1607_,
        );
        return v___x_1608_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(
    mut v_init_1609_: *mut leanh::LeanObject,
    mut v_x_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1610_) == 0 {
                    v_k_1611_ = leanh::lean_ctor_get(v_x_1610_, 1);
                    v_v_1612_ = leanh::lean_ctor_get(v_x_1610_, 2);
                    v_l_1613_ = leanh::lean_ctor_get(v_x_1610_, 3);
                    v_r_1614_ = leanh::lean_ctor_get(v_x_1610_, 4);
                    v___x_1615_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v_init_1609_, v_r_1614_);
                    leanh::lean_inc(v_v_1612_);
                    leanh::lean_inc(v_k_1611_);
                    v___x_1616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1616_, 0, v_k_1611_);
                    leanh::lean_ctor_set(v___x_1616_, 1, v_v_1612_);
                    v___x_1617_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
                    leanh::lean_ctor_set(v___x_1617_, 1, v___x_1615_);
                    v_init_1609_ = v___x_1617_;
                    v_x_1610_ = v_l_1613_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1609_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0___boxed(
    mut v_init_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1621_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(
            v_init_1619_,
            v_x_1620_,
        );
    leanh::lean_dec(v_x_1620_);
    return v_res_1621_;
}
pub unsafe fn _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = leanh::lean_unsigned_to_nat(10);
    v___x_1632_ = lean_nat_to_int(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr___redArg(
    mut v_x_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Lean_instReprLeanOptions_repr___redArg___closed__3;
    v___x_1638_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptions_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptions_repr___redArg___closed__4_once),
        _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4,
    );
    v___x_1639_ = leanh::lean_unsigned_to_nat(0);
    v___x_1640_ = l_Lean_instReprLeanOptions_repr___redArg___closed__6;
    v___x_1641_ = leanh::lean_box(0);
    v___x_1642_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(
            v___x_1641_,
            v_x_1636_,
        );
    v___x_1643_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v___x_1642_);
    v___x_1644_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1644_, 0, v___x_1640_);
    leanh::lean_ctor_set(v___x_1644_, 1, v___x_1643_);
    v___x_1645_ = l_Repr_addAppParen(v___x_1644_, v___x_1639_);
    v___x_1646_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1646_, 0, v___x_1638_);
    leanh::lean_ctor_set(v___x_1646_, 1, v___x_1645_);
    v___x_1647_ = 0;
    v___x_1648_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1648_, 0, v___x_1646_);
    leanh::lean_ctor_set_uint8(
        v___x_1648_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1647_,
    );
    v___x_1649_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1649_, 0, v___x_1637_);
    leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
    v___x_1650_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__15_once),
        _init_l_Lean_instReprLeanOption_repr___redArg___closed__15,
    );
    v___x_1651_ = l_Lean_instReprLeanOption_repr___redArg___closed__16;
    v___x_1652_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1652_, 0, v___x_1651_);
    leanh::lean_ctor_set(v___x_1652_, 1, v___x_1649_);
    v___x_1653_ = l_Lean_instReprLeanOption_repr___redArg___closed__17;
    v___x_1654_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1654_, 0, v___x_1652_);
    leanh::lean_ctor_set(v___x_1654_, 1, v___x_1653_);
    v___x_1655_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1655_, 0, v___x_1650_);
    leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
    v___x_1656_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1656_, 0, v___x_1655_);
    leanh::lean_ctor_set_uint8(
        v___x_1656_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1647_,
    );
    return v___x_1656_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr___redArg___boxed(
    mut v_x_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_1657_);
    leanh::lean_dec(v_x_1657_);
    return v_res_1658_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr(
    mut v_x_1659_: *mut leanh::LeanObject,
    mut v_prec_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_1659_);
    return v___x_1661_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr___boxed(
    mut v_x_1662_: *mut leanh::LeanObject,
    mut v_prec_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_instReprLeanOptions_repr(v_x_1662_, v_prec_1663_);
    leanh::lean_dec(v_prec_1663_);
    leanh::lean_dec(v_x_1662_);
    return v_res_1664_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(
    mut v_a_1665_: *mut leanh::LeanObject,
    mut v_n_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v_a_1665_);
    return v___x_1667_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___boxed(
    mut v_a_1668_: *mut leanh::LeanObject,
    mut v_n_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(v_a_1668_, v_n_1669_);
    leanh::lean_dec(v_n_1669_);
    return v_res_1670_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(
    mut v_x_1671_: *mut leanh::LeanObject,
    mut v_x_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_x_1671_);
    return v___x_1673_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___boxed(
    mut v_x_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1676_ =
        l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(
            v_x_1674_, v_x_1675_,
        );
    leanh::lean_dec(v_x_1675_);
    return v_res_1676_;
}
pub unsafe fn _init_l_Lean_instEmptyCollectionLeanOptions() -> *mut leanh::LeanObject {
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1679_ = leanh::lean_box(1);
    return v___x_1679_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(
    mut v_as_1680_: *mut leanh::LeanObject,
    mut v_i_1681_: usize,
    mut v_stop_1682_: usize,
    mut v_b_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: usize = 0;
    let mut v___x_1690_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1684_ = lean_usize_dec_eq(v_i_1681_, v_stop_1682_);
                if v___x_1684_ == 0 {
                    v___x_1685_ = lean_array_uget_borrowed(v_as_1680_, v_i_1681_);
                    v_name_1686_ = leanh::lean_ctor_get(v___x_1685_, 0);
                    v_value_1687_ = leanh::lean_ctor_get(v___x_1685_, 1);
                    leanh::lean_inc_ref(v_value_1687_);
                    leanh::lean_inc(v_name_1686_);
                    v___x_1688_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1686_, v_value_1687_, v_b_1683_);
                    v___x_1689_ = 1usize;
                    v___x_1690_ = lean_usize_add(v_i_1681_, v___x_1689_);
                    v_i_1681_ = v___x_1690_;
                    v_b_1683_ = v___x_1688_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1683_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0___boxed(
    mut v_as_1692_: *mut leanh::LeanObject,
    mut v_i_1693_: *mut leanh::LeanObject,
    mut v_stop_1694_: *mut leanh::LeanObject,
    mut v_b_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1696_: usize = 0;
    let mut v_stop_boxed_1697_: usize = 0;
    let mut v_res_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1696_ = leanh::lean_unbox_usize(v_i_1693_);
    leanh::lean_dec(v_i_1693_);
    v_stop_boxed_1697_ = leanh::lean_unbox_usize(v_stop_1694_);
    leanh::lean_dec(v_stop_1694_);
    v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_as_1692_, v_i_boxed_1696_, v_stop_boxed_1697_, v_b_1695_);
    leanh::lean_dec_ref(v_as_1692_);
    return v_res_1698_;
}
pub unsafe fn l_Lean_LeanOptions_ofArray(
    mut v_opts_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: u8 = 0;
    v___x_1700_ = leanh::lean_box(1);
    v___x_1701_ = leanh::lean_unsigned_to_nat(0);
    v___x_1702_ = lean_array_get_size(v_opts_1699_);
    v___x_1703_ = lean_nat_dec_lt(v___x_1701_, v___x_1702_);
    if v___x_1703_ == 0 {
        return v___x_1700_;
    } else {
        let mut v___x_1704_: u8 = 0;
        v___x_1704_ = lean_nat_dec_le(v___x_1702_, v___x_1702_);
        if v___x_1704_ == 0 {
            if v___x_1703_ == 0 {
                return v___x_1700_;
            } else {
                let mut v___x_1705_: usize = 0;
                let mut v___x_1706_: usize = 0;
                let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1705_ = 0usize;
                v___x_1706_ = lean_usize_of_nat(v___x_1702_);
                v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_1699_, v___x_1705_, v___x_1706_, v___x_1700_);
                return v___x_1707_;
            }
        } else {
            let mut v___x_1708_: usize = 0;
            let mut v___x_1709_: usize = 0;
            let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1708_ = 0usize;
            v___x_1709_ = lean_usize_of_nat(v___x_1702_);
            v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_1699_, v___x_1708_, v___x_1709_, v___x_1700_);
            return v___x_1710_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_ofArray___boxed(
    mut v_opts_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lean_LeanOptions_ofArray(v_opts_1711_);
    leanh::lean_dec_ref(v_opts_1711_);
    return v_res_1712_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(
    mut v_b_u2082_1713_: *mut leanh::LeanObject,
    mut v_k_1714_: *mut leanh::LeanObject,
    mut v_t_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: u8 = 0;
    let mut v_impl_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1715_) == 0 {
                    v_size_1716_ = leanh::lean_ctor_get(v_t_1715_, 0);
                    v_k_1717_ = leanh::lean_ctor_get(v_t_1715_, 1);
                    v_v_1718_ = leanh::lean_ctor_get(v_t_1715_, 2);
                    v_l_1719_ = leanh::lean_ctor_get(v_t_1715_, 3);
                    v_r_1720_ = leanh::lean_ctor_get(v_t_1715_, 4);
                    v_isSharedCheck_1732_ = (!leanh::lean_is_exclusive(v_t_1715_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1722_ = v_t_1715_;
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1720_);
                        leanh::lean_inc(v_l_1719_);
                        leanh::lean_inc(v_v_1718_);
                        leanh::lean_inc(v_k_1717_);
                        leanh::lean_inc(v_size_1716_);
                        leanh::lean_dec(v_t_1715_);
                        v___x_1722_ = leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1733_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1734_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_1734_, 0, v___x_1733_);
                    leanh::lean_ctor_set(v___x_1734_, 1, v_k_1714_);
                    leanh::lean_ctor_set(v___x_1734_, 2, v_b_u2082_1713_);
                    leanh::lean_ctor_set(v___x_1734_, 3, v_t_1715_);
                    leanh::lean_ctor_set(v___x_1734_, 4, v_t_1715_);
                    return v___x_1734_;
                }
            }
            1 => {
                v___x_1724_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1714_, v_k_1717_);
                match v___x_1724_ {
                    0 => {
                        leanh::lean_del_object(v___x_1722_);
                        leanh::lean_dec(v_size_1716_);
                        v_impl_1725_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_1713_, v_k_1714_, v_l_1719_);
                        v___x_1726_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_1717_,
                            v_v_1718_,
                            v_impl_1725_,
                            v_r_1720_,
                        );
                        return v___x_1726_;
                    }
                    1 => {
                        leanh::lean_dec(v_v_1718_);
                        leanh::lean_dec(v_k_1717_);
                        if v_isShared_1723_ == 0 {
                            leanh::lean_ctor_set(v___x_1722_, 2, v_b_u2082_1713_);
                            leanh::lean_ctor_set(v___x_1722_, 1, v_k_1714_);
                            v___x_1728_ = v___x_1722_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1729_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_size_1716_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_k_1714_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_b_u2082_1713_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_l_1719_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_r_1720_);
                            v___x_1728_ = v_reuseFailAlloc_1729_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_1722_);
                        leanh::lean_dec(v_size_1716_);
                        v_impl_1730_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_b_u2082_1713_, v_k_1714_, v_r_1720_);
                        v___x_1731_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_1717_,
                            v_v_1718_,
                            v_l_1719_,
                            v_impl_1730_,
                        );
                        return v___x_1731_;
                    }
                }
            }
            2 => {
                return v___x_1728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(
    mut v_init_1735_: *mut leanh::LeanObject,
    mut v_x_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1736_) == 0 {
                    v_k_1737_ = leanh::lean_ctor_get(v_x_1736_, 1);
                    leanh::lean_inc(v_k_1737_);
                    v_v_1738_ = leanh::lean_ctor_get(v_x_1736_, 2);
                    leanh::lean_inc(v_v_1738_);
                    v_l_1739_ = leanh::lean_ctor_get(v_x_1736_, 3);
                    leanh::lean_inc(v_l_1739_);
                    v_r_1740_ = leanh::lean_ctor_get(v_x_1736_, 4);
                    leanh::lean_inc(v_r_1740_);
                    leanh::lean_dec_ref_known(v_x_1736_, 5);
                    v___x_1741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_1735_, v_l_1739_);
                    v___x_1742_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(v_v_1738_, v_k_1737_, v___x_1741_);
                    v_init_1735_ = v___x_1742_;
                    v_x_1736_ = v_r_1740_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1735_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_append(
    mut v_self_1744_: *mut leanh::LeanObject,
    mut v_new_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_self_1744_, v_new_1745_);
    return v___x_1746_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0(
    mut v_b_u2082_1747_: *mut leanh::LeanObject,
    mut v_k_1748_: *mut leanh::LeanObject,
    mut v_t_1749_: *mut leanh::LeanObject,
    mut v_hl_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ =
        l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(
            v_b_u2082_1747_,
            v_k_1748_,
            v_t_1749_,
        );
    return v___x_1751_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1(
    mut v_init_1752_: *mut leanh::LeanObject,
    mut v_t_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_1752_, v_t_1753_);
    return v___x_1754_;
}
pub unsafe fn l_Lean_LeanOptions_appendArray(
    mut v_self_1757_: *mut leanh::LeanObject,
    mut v_new_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    v___x_1759_ = leanh::lean_unsigned_to_nat(0);
    v___x_1760_ = lean_array_get_size(v_new_1758_);
    v___x_1761_ = lean_nat_dec_lt(v___x_1759_, v___x_1760_);
    if v___x_1761_ == 0 {
        return v_self_1757_;
    } else {
        let mut v___x_1762_: u8 = 0;
        v___x_1762_ = lean_nat_dec_le(v___x_1760_, v___x_1760_);
        if v___x_1762_ == 0 {
            if v___x_1761_ == 0 {
                return v_self_1757_;
            } else {
                let mut v___x_1763_: usize = 0;
                let mut v___x_1764_: usize = 0;
                let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1763_ = 0usize;
                v___x_1764_ = lean_usize_of_nat(v___x_1760_);
                v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_1758_, v___x_1763_, v___x_1764_, v_self_1757_);
                return v___x_1765_;
            }
        } else {
            let mut v___x_1766_: usize = 0;
            let mut v___x_1767_: usize = 0;
            let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1766_ = 0usize;
            v___x_1767_ = lean_usize_of_nat(v___x_1760_);
            v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_1758_, v___x_1766_, v___x_1767_, v_self_1757_);
            return v___x_1768_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_appendArray___boxed(
    mut v_self_1769_: *mut leanh::LeanObject,
    mut v_new_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Lean_LeanOptions_appendArray(v_self_1769_, v_new_1770_);
    leanh::lean_dec_ref(v_new_1770_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(
    mut v_o_1777_: *mut leanh::LeanObject,
    mut v_k_1778_: *mut leanh::LeanObject,
    mut v_v_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1781_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1780_ = leanh::lean_ctor_get(v_o_1777_, 0);
                v_hasTrace_1781_ = leanh::lean_ctor_get_uint8(
                    v_o_1777_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1794_ = (!leanh::lean_is_exclusive(v_o_1777_)) as u8;
                if v_isSharedCheck_1794_ == 0 {
                    v___x_1783_ = v_o_1777_;
                    v_isShared_1784_ = v_isSharedCheck_1794_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_1780_);
                    leanh::lean_dec(v_o_1777_);
                    v___x_1783_ = leanh::lean_box(0);
                    v_isShared_1784_ = v_isSharedCheck_1794_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_k_1778_);
                v___x_1785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1778_, v_v_1779_, v_map_1780_);
                if v_hasTrace_1781_ == 0 {
                    v___x_1786_ =
                        l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1;
                    v___x_1787_ = l_Lean_Name_isPrefixOf(v___x_1786_, v_k_1778_);
                    leanh::lean_dec(v_k_1778_);
                    if v_isShared_1784_ == 0 {
                        leanh::lean_ctor_set(v___x_1783_, 0, v___x_1785_);
                        v___x_1789_ = v___x_1783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1790_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1785_);
                        v___x_1789_ = v_reuseFailAlloc_1790_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1778_);
                    if v_isShared_1784_ == 0 {
                        leanh::lean_ctor_set(v___x_1783_, 0, v___x_1785_);
                        v___x_1792_ = v___x_1783_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1793_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1785_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1793_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1781_,
                        );
                        v___x_1792_ = v_reuseFailAlloc_1793_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1789_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1787_,
                );
                return v___x_1789_;
            }
            3 => {
                return v___x_1792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(
    mut v_init_1795_: *mut leanh::LeanObject,
    mut v_x_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1796_) == 0 {
                    v_k_1797_ = leanh::lean_ctor_get(v_x_1796_, 1);
                    leanh::lean_inc(v_k_1797_);
                    v_v_1798_ = leanh::lean_ctor_get(v_x_1796_, 2);
                    leanh::lean_inc(v_v_1798_);
                    v_l_1799_ = leanh::lean_ctor_get(v_x_1796_, 3);
                    leanh::lean_inc(v_l_1799_);
                    v_r_1800_ = leanh::lean_ctor_get(v_x_1796_, 4);
                    leanh::lean_inc(v_r_1800_);
                    leanh::lean_dec_ref_known(v_x_1796_, 5);
                    v___x_1801_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_init_1795_, v_l_1799_);
                    v_a_1802_ = leanh::lean_ctor_get(v___x_1801_, 0);
                    leanh::lean_inc(v_a_1802_);
                    leanh::lean_dec_ref(v___x_1801_);
                    v___x_1803_ = l_Lean_LeanOptionValue_toDataValue(v_v_1798_);
                    v___x_1804_ = l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(
                        v_a_1802_,
                        v_k_1797_,
                        v___x_1803_,
                    );
                    v_init_1795_ = v___x_1804_;
                    v_x_1796_ = v_r_1800_;
                    state = 0;
                    continue;
                } else {
                    v___x_1806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1806_, 0, v_init_1795_);
                    return v___x_1806_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_toOptions(
    mut v_leanOptions_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_options_1808_ = l_Lean_Options_empty;
    v___x_1809_ =
        l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(
            v_options_1808_,
            v_leanOptions_1807_,
        );
    v_a_1810_ = leanh::lean_ctor_get(v___x_1809_, 0);
    leanh::lean_inc(v_a_1810_);
    leanh::lean_dec_ref(v___x_1809_);
    return v_a_1810_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(
    mut v_k_1811_: *mut leanh::LeanObject,
    mut v_v_1812_: *mut leanh::LeanObject,
    mut v_t_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v_impl_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v_size_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v_unused_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_unused_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1924_: u8 = 0;
    let mut v_unused_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v_k_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_unused_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v_size_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_unused_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2031_: u8 = 0;
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_unused_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v_k_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_unused_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_unused_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1813_) == 0 {
                    v_size_1814_ = leanh::lean_ctor_get(v_t_1813_, 0);
                    v_k_1815_ = leanh::lean_ctor_get(v_t_1813_, 1);
                    v_v_1816_ = leanh::lean_ctor_get(v_t_1813_, 2);
                    v_l_1817_ = leanh::lean_ctor_get(v_t_1813_, 3);
                    v_r_1818_ = leanh::lean_ctor_get(v_t_1813_, 4);
                    v_isSharedCheck_2098_ = (!leanh::lean_is_exclusive(v_t_1813_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_1820_ = v_t_1813_;
                        v_isShared_1821_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1818_);
                        leanh::lean_inc(v_l_1817_);
                        leanh::lean_inc(v_v_1816_);
                        leanh::lean_inc(v_k_1815_);
                        leanh::lean_inc(v_size_1814_);
                        leanh::lean_dec(v_t_1813_);
                        v___x_1820_ = leanh::lean_box(0);
                        v_isShared_1821_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2099_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2100_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
                    leanh::lean_ctor_set(v___x_2100_, 1, v_k_1811_);
                    leanh::lean_ctor_set(v___x_2100_, 2, v_v_1812_);
                    leanh::lean_ctor_set(v___x_2100_, 3, v_t_1813_);
                    leanh::lean_ctor_set(v___x_2100_, 4, v_t_1813_);
                    return v___x_2100_;
                }
            }
            1 => {
                v___x_1822_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1811_, v_k_1815_);
                match v___x_1822_ {
                    0 => {
                        leanh::lean_dec(v_size_1814_);
                        v_impl_1823_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1811_, v_v_1812_, v_l_1817_);
                        v___x_1824_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_1818_) == 0 {
                            v_size_1825_ = leanh::lean_ctor_get(v_r_1818_, 0);
                            v_size_1826_ = leanh::lean_ctor_get(v_impl_1823_, 0);
                            leanh::lean_inc(v_size_1826_);
                            v_k_1827_ = leanh::lean_ctor_get(v_impl_1823_, 1);
                            leanh::lean_inc(v_k_1827_);
                            v_v_1828_ = leanh::lean_ctor_get(v_impl_1823_, 2);
                            leanh::lean_inc(v_v_1828_);
                            v_l_1829_ = leanh::lean_ctor_get(v_impl_1823_, 3);
                            leanh::lean_inc(v_l_1829_);
                            v_r_1830_ = leanh::lean_ctor_get(v_impl_1823_, 4);
                            leanh::lean_inc(v_r_1830_);
                            v___x_1831_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1832_ = lean_nat_mul(v___x_1831_, v_size_1825_);
                            v___x_1833_ = lean_nat_dec_lt(v___x_1832_, v_size_1826_);
                            leanh::lean_dec(v___x_1832_);
                            if v___x_1833_ == 0 {
                                leanh::lean_dec(v_r_1830_);
                                leanh::lean_dec(v_l_1829_);
                                leanh::lean_dec(v_v_1828_);
                                leanh::lean_dec(v_k_1827_);
                                v___x_1834_ = lean_nat_add(v___x_1824_, v_size_1826_);
                                leanh::lean_dec(v_size_1826_);
                                v___x_1835_ = lean_nat_add(v___x_1834_, v_size_1825_);
                                leanh::lean_dec(v___x_1834_);
                                if v_isShared_1821_ == 0 {
                                    leanh::lean_ctor_set(v___x_1820_, 3, v_impl_1823_);
                                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1835_);
                                    v___x_1837_ = v___x_1820_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1838_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        0,
                                        v___x_1835_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        1,
                                        v_k_1815_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        2,
                                        v_v_1816_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        3,
                                        v_impl_1823_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        4,
                                        v_r_1818_,
                                    );
                                    v___x_1837_ = v_reuseFailAlloc_1838_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1904_ =
                                    (!leanh::lean_is_exclusive(v_impl_1823_)) as u8;
                                if v_isSharedCheck_1904_ == 0 {
                                    v_unused_1905_ = leanh::lean_ctor_get(v_impl_1823_, 4);
                                    leanh::lean_dec(v_unused_1905_);
                                    v_unused_1906_ = leanh::lean_ctor_get(v_impl_1823_, 3);
                                    leanh::lean_dec(v_unused_1906_);
                                    v_unused_1907_ = leanh::lean_ctor_get(v_impl_1823_, 2);
                                    leanh::lean_dec(v_unused_1907_);
                                    v_unused_1908_ = leanh::lean_ctor_get(v_impl_1823_, 1);
                                    leanh::lean_dec(v_unused_1908_);
                                    v_unused_1909_ = leanh::lean_ctor_get(v_impl_1823_, 0);
                                    leanh::lean_dec(v_unused_1909_);
                                    v___x_1840_ = v_impl_1823_;
                                    v_isShared_1841_ = v_isSharedCheck_1904_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_1823_);
                                    v___x_1840_ = leanh::lean_box(0);
                                    v_isShared_1841_ = v_isSharedCheck_1904_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1910_ = leanh::lean_ctor_get(v_impl_1823_, 3);
                            leanh::lean_inc(v_l_1910_);
                            if leanh::lean_obj_tag(v_l_1910_) == 0 {
                                v_r_1911_ = leanh::lean_ctor_get(v_impl_1823_, 4);
                                v_k_1912_ = leanh::lean_ctor_get(v_impl_1823_, 1);
                                v_v_1913_ = leanh::lean_ctor_get(v_impl_1823_, 2);
                                v_isSharedCheck_1924_ =
                                    (!leanh::lean_is_exclusive(v_impl_1823_)) as u8;
                                if v_isSharedCheck_1924_ == 0 {
                                    v_unused_1925_ = leanh::lean_ctor_get(v_impl_1823_, 3);
                                    leanh::lean_dec(v_unused_1925_);
                                    v_unused_1926_ = leanh::lean_ctor_get(v_impl_1823_, 0);
                                    leanh::lean_dec(v_unused_1926_);
                                    v___x_1915_ = v_impl_1823_;
                                    v_isShared_1916_ = v_isSharedCheck_1924_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_1911_);
                                    leanh::lean_inc(v_v_1913_);
                                    leanh::lean_inc(v_k_1912_);
                                    leanh::lean_dec(v_impl_1823_);
                                    v___x_1915_ = leanh::lean_box(0);
                                    v_isShared_1916_ = v_isSharedCheck_1924_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1927_ = leanh::lean_ctor_get(v_impl_1823_, 4);
                                leanh::lean_inc(v_r_1927_);
                                if leanh::lean_obj_tag(v_r_1927_) == 0 {
                                    v_k_1928_ = leanh::lean_ctor_get(v_impl_1823_, 1);
                                    v_v_1929_ = leanh::lean_ctor_get(v_impl_1823_, 2);
                                    v_isSharedCheck_1952_ =
                                        (!leanh::lean_is_exclusive(v_impl_1823_)) as u8;
                                    if v_isSharedCheck_1952_ == 0 {
                                        v_unused_1953_ =
                                            leanh::lean_ctor_get(v_impl_1823_, 4);
                                        leanh::lean_dec(v_unused_1953_);
                                        v_unused_1954_ =
                                            leanh::lean_ctor_get(v_impl_1823_, 3);
                                        leanh::lean_dec(v_unused_1954_);
                                        v_unused_1955_ =
                                            leanh::lean_ctor_get(v_impl_1823_, 0);
                                        leanh::lean_dec(v_unused_1955_);
                                        v___x_1931_ = v_impl_1823_;
                                        v_isShared_1932_ = v_isSharedCheck_1952_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_1929_);
                                        leanh::lean_inc(v_k_1928_);
                                        leanh::lean_dec(v_impl_1823_);
                                        v___x_1931_ = leanh::lean_box(0);
                                        v_isShared_1932_ = v_isSharedCheck_1952_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1956_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1821_ == 0 {
                                        leanh::lean_ctor_set(v___x_1820_, 4, v_r_1927_);
                                        leanh::lean_ctor_set(v___x_1820_, 3, v_impl_1823_);
                                        leanh::lean_ctor_set(v___x_1820_, 0, v___x_1956_);
                                        v___x_1958_ = v___x_1820_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1959_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            0,
                                            v___x_1956_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            1,
                                            v_k_1815_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            2,
                                            v_v_1816_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            3,
                                            v_impl_1823_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            4,
                                            v_r_1927_,
                                        );
                                        v___x_1958_ = v_reuseFailAlloc_1959_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_1816_);
                        leanh::lean_dec(v_k_1815_);
                        if v_isShared_1821_ == 0 {
                            leanh::lean_ctor_set(v___x_1820_, 2, v_v_1812_);
                            leanh::lean_ctor_set(v___x_1820_, 1, v_k_1811_);
                            v___x_1961_ = v___x_1820_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1962_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_size_1814_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_k_1811_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_v_1812_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_l_1817_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_r_1818_);
                            v___x_1961_ = v_reuseFailAlloc_1962_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_1814_);
                        v_impl_1963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1811_, v_v_1812_, v_r_1818_);
                        v___x_1964_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_1817_) == 0 {
                            v_size_1965_ = leanh::lean_ctor_get(v_l_1817_, 0);
                            v_size_1966_ = leanh::lean_ctor_get(v_impl_1963_, 0);
                            leanh::lean_inc(v_size_1966_);
                            v_k_1967_ = leanh::lean_ctor_get(v_impl_1963_, 1);
                            leanh::lean_inc(v_k_1967_);
                            v_v_1968_ = leanh::lean_ctor_get(v_impl_1963_, 2);
                            leanh::lean_inc(v_v_1968_);
                            v_l_1969_ = leanh::lean_ctor_get(v_impl_1963_, 3);
                            leanh::lean_inc(v_l_1969_);
                            v_r_1970_ = leanh::lean_ctor_get(v_impl_1963_, 4);
                            leanh::lean_inc(v_r_1970_);
                            v___x_1971_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1972_ = lean_nat_mul(v___x_1971_, v_size_1965_);
                            v___x_1973_ = lean_nat_dec_lt(v___x_1972_, v_size_1966_);
                            leanh::lean_dec(v___x_1972_);
                            if v___x_1973_ == 0 {
                                leanh::lean_dec(v_r_1970_);
                                leanh::lean_dec(v_l_1969_);
                                leanh::lean_dec(v_v_1968_);
                                leanh::lean_dec(v_k_1967_);
                                v___x_1974_ = lean_nat_add(v___x_1964_, v_size_1965_);
                                v___x_1975_ = lean_nat_add(v___x_1974_, v_size_1966_);
                                leanh::lean_dec(v_size_1966_);
                                leanh::lean_dec(v___x_1974_);
                                if v_isShared_1821_ == 0 {
                                    leanh::lean_ctor_set(v___x_1820_, 4, v_impl_1963_);
                                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1975_);
                                    v___x_1977_ = v___x_1820_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1978_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        0,
                                        v___x_1975_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        1,
                                        v_k_1815_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        2,
                                        v_v_1816_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        3,
                                        v_l_1817_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        4,
                                        v_impl_1963_,
                                    );
                                    v___x_1977_ = v_reuseFailAlloc_1978_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2042_ =
                                    (!leanh::lean_is_exclusive(v_impl_1963_)) as u8;
                                if v_isSharedCheck_2042_ == 0 {
                                    v_unused_2043_ = leanh::lean_ctor_get(v_impl_1963_, 4);
                                    leanh::lean_dec(v_unused_2043_);
                                    v_unused_2044_ = leanh::lean_ctor_get(v_impl_1963_, 3);
                                    leanh::lean_dec(v_unused_2044_);
                                    v_unused_2045_ = leanh::lean_ctor_get(v_impl_1963_, 2);
                                    leanh::lean_dec(v_unused_2045_);
                                    v_unused_2046_ = leanh::lean_ctor_get(v_impl_1963_, 1);
                                    leanh::lean_dec(v_unused_2046_);
                                    v_unused_2047_ = leanh::lean_ctor_get(v_impl_1963_, 0);
                                    leanh::lean_dec(v_unused_2047_);
                                    v___x_1980_ = v_impl_1963_;
                                    v_isShared_1981_ = v_isSharedCheck_2042_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_1963_);
                                    v___x_1980_ = leanh::lean_box(0);
                                    v_isShared_1981_ = v_isSharedCheck_2042_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2048_ = leanh::lean_ctor_get(v_impl_1963_, 3);
                            leanh::lean_inc(v_l_2048_);
                            if leanh::lean_obj_tag(v_l_2048_) == 0 {
                                v_r_2049_ = leanh::lean_ctor_get(v_impl_1963_, 4);
                                v_k_2050_ = leanh::lean_ctor_get(v_impl_1963_, 1);
                                v_v_2051_ = leanh::lean_ctor_get(v_impl_1963_, 2);
                                v_isSharedCheck_2074_ =
                                    (!leanh::lean_is_exclusive(v_impl_1963_)) as u8;
                                if v_isSharedCheck_2074_ == 0 {
                                    v_unused_2075_ = leanh::lean_ctor_get(v_impl_1963_, 3);
                                    leanh::lean_dec(v_unused_2075_);
                                    v_unused_2076_ = leanh::lean_ctor_get(v_impl_1963_, 0);
                                    leanh::lean_dec(v_unused_2076_);
                                    v___x_2053_ = v_impl_1963_;
                                    v_isShared_2054_ = v_isSharedCheck_2074_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_2049_);
                                    leanh::lean_inc(v_v_2051_);
                                    leanh::lean_inc(v_k_2050_);
                                    leanh::lean_dec(v_impl_1963_);
                                    v___x_2053_ = leanh::lean_box(0);
                                    v_isShared_2054_ = v_isSharedCheck_2074_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_2077_ = leanh::lean_ctor_get(v_impl_1963_, 4);
                                leanh::lean_inc(v_r_2077_);
                                if leanh::lean_obj_tag(v_r_2077_) == 0 {
                                    v_k_2078_ = leanh::lean_ctor_get(v_impl_1963_, 1);
                                    v_v_2079_ = leanh::lean_ctor_get(v_impl_1963_, 2);
                                    v_isSharedCheck_2090_ =
                                        (!leanh::lean_is_exclusive(v_impl_1963_)) as u8;
                                    if v_isSharedCheck_2090_ == 0 {
                                        v_unused_2091_ =
                                            leanh::lean_ctor_get(v_impl_1963_, 4);
                                        leanh::lean_dec(v_unused_2091_);
                                        v_unused_2092_ =
                                            leanh::lean_ctor_get(v_impl_1963_, 3);
                                        leanh::lean_dec(v_unused_2092_);
                                        v_unused_2093_ =
                                            leanh::lean_ctor_get(v_impl_1963_, 0);
                                        leanh::lean_dec(v_unused_2093_);
                                        v___x_2081_ = v_impl_1963_;
                                        v_isShared_2082_ = v_isSharedCheck_2090_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_2079_);
                                        leanh::lean_inc(v_k_2078_);
                                        leanh::lean_dec(v_impl_1963_);
                                        v___x_2081_ = leanh::lean_box(0);
                                        v_isShared_2082_ = v_isSharedCheck_2090_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_2094_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1821_ == 0 {
                                        leanh::lean_ctor_set(v___x_1820_, 4, v_impl_1963_);
                                        leanh::lean_ctor_set(v___x_1820_, 3, v_r_2077_);
                                        leanh::lean_ctor_set(v___x_1820_, 0, v___x_2094_);
                                        v___x_2096_ = v___x_1820_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2097_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            0,
                                            v___x_2094_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            1,
                                            v_k_1815_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            2,
                                            v_v_1816_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            3,
                                            v_r_2077_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            4,
                                            v_impl_1963_,
                                        );
                                        v___x_2096_ = v_reuseFailAlloc_2097_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1837_;
            }
            3 => {
                v_size_1842_ = leanh::lean_ctor_get(v_l_1829_, 0);
                v_size_1843_ = leanh::lean_ctor_get(v_r_1830_, 0);
                v_k_1844_ = leanh::lean_ctor_get(v_r_1830_, 1);
                v_v_1845_ = leanh::lean_ctor_get(v_r_1830_, 2);
                v_l_1846_ = leanh::lean_ctor_get(v_r_1830_, 3);
                v_r_1847_ = leanh::lean_ctor_get(v_r_1830_, 4);
                v___x_1848_ = leanh::lean_unsigned_to_nat(2);
                v___x_1849_ = lean_nat_mul(v___x_1848_, v_size_1842_);
                v___x_1850_ = lean_nat_dec_lt(v_size_1843_, v___x_1849_);
                leanh::lean_dec(v___x_1849_);
                if v___x_1850_ == 0 {
                    leanh::lean_inc(v_r_1847_);
                    leanh::lean_inc(v_l_1846_);
                    leanh::lean_inc(v_v_1845_);
                    leanh::lean_inc(v_k_1844_);
                    v_isSharedCheck_1879_ = (!leanh::lean_is_exclusive(v_r_1830_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v_unused_1880_ = leanh::lean_ctor_get(v_r_1830_, 4);
                        leanh::lean_dec(v_unused_1880_);
                        v_unused_1881_ = leanh::lean_ctor_get(v_r_1830_, 3);
                        leanh::lean_dec(v_unused_1881_);
                        v_unused_1882_ = leanh::lean_ctor_get(v_r_1830_, 2);
                        leanh::lean_dec(v_unused_1882_);
                        v_unused_1883_ = leanh::lean_ctor_get(v_r_1830_, 1);
                        leanh::lean_dec(v_unused_1883_);
                        v_unused_1884_ = leanh::lean_ctor_get(v_r_1830_, 0);
                        leanh::lean_dec(v_unused_1884_);
                        v___x_1852_ = v_r_1830_;
                        v_isShared_1853_ = v_isSharedCheck_1879_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_1830_);
                        v___x_1852_ = leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1879_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1820_);
                    v___x_1885_ = lean_nat_add(v___x_1824_, v_size_1826_);
                    leanh::lean_dec(v_size_1826_);
                    v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1825_);
                    leanh::lean_dec(v___x_1885_);
                    v___x_1887_ = lean_nat_add(v___x_1824_, v_size_1825_);
                    v___x_1888_ = lean_nat_add(v___x_1887_, v_size_1843_);
                    leanh::lean_dec(v___x_1887_);
                    leanh::lean_inc_ref(v_r_1818_);
                    if v_isShared_1841_ == 0 {
                        leanh::lean_ctor_set(v___x_1840_, 4, v_r_1818_);
                        leanh::lean_ctor_set(v___x_1840_, 3, v_r_1830_);
                        leanh::lean_ctor_set(v___x_1840_, 2, v_v_1816_);
                        leanh::lean_ctor_set(v___x_1840_, 1, v_k_1815_);
                        leanh::lean_ctor_set(v___x_1840_, 0, v___x_1888_);
                        v___x_1890_ = v___x_1840_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1903_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1888_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1815_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1816_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_r_1830_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_r_1818_);
                        v___x_1890_ = v_reuseFailAlloc_1903_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1854_ = lean_nat_add(v___x_1824_, v_size_1826_);
                leanh::lean_dec(v_size_1826_);
                v___x_1855_ = lean_nat_add(v___x_1854_, v_size_1825_);
                leanh::lean_dec(v___x_1854_);
                v___x_1867_ = lean_nat_add(v___x_1824_, v_size_1842_);
                if leanh::lean_obj_tag(v_l_1846_) == 0 {
                    v_size_1877_ = leanh::lean_ctor_get(v_l_1846_, 0);
                    leanh::lean_inc(v_size_1877_);
                    v___y_1869_ = v_size_1877_;
                    state = 8;
                    continue;
                } else {
                    v___x_1878_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1869_ = v___x_1878_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1860_ = lean_nat_add(v___y_1858_, v___y_1859_);
                leanh::lean_dec(v___y_1859_);
                leanh::lean_dec(v___y_1858_);
                if v_isShared_1853_ == 0 {
                    leanh::lean_ctor_set(v___x_1852_, 4, v_r_1818_);
                    leanh::lean_ctor_set(v___x_1852_, 3, v_r_1847_);
                    leanh::lean_ctor_set(v___x_1852_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v___x_1852_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v___x_1852_, 0, v___x_1860_);
                    v___x_1862_ = v___x_1852_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_r_1847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_r_1818_);
                    v___x_1862_ = v_reuseFailAlloc_1866_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1841_ == 0 {
                    leanh::lean_ctor_set(v___x_1840_, 4, v___x_1862_);
                    leanh::lean_ctor_set(v___x_1840_, 3, v___y_1857_);
                    leanh::lean_ctor_set(v___x_1840_, 2, v_v_1845_);
                    leanh::lean_ctor_set(v___x_1840_, 1, v_k_1844_);
                    leanh::lean_ctor_set(v___x_1840_, 0, v___x_1855_);
                    v___x_1864_ = v___x_1840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_k_1844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_v_1845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 3, v___y_1857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 4, v___x_1862_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1864_;
            }
            8 => {
                v___x_1870_ = lean_nat_add(v___x_1867_, v___y_1869_);
                leanh::lean_dec(v___y_1869_);
                leanh::lean_dec(v___x_1867_);
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 4, v_l_1846_);
                    leanh::lean_ctor_set(v___x_1820_, 3, v_l_1829_);
                    leanh::lean_ctor_set(v___x_1820_, 2, v_v_1828_);
                    leanh::lean_ctor_set(v___x_1820_, 1, v_k_1827_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1870_);
                    v___x_1872_ = v___x_1820_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1876_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_k_1827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_v_1828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_l_1829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_l_1846_);
                    v___x_1872_ = v_reuseFailAlloc_1876_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1873_ = lean_nat_add(v___x_1824_, v_size_1825_);
                if leanh::lean_obj_tag(v_r_1847_) == 0 {
                    v_size_1874_ = leanh::lean_ctor_get(v_r_1847_, 0);
                    leanh::lean_inc(v_size_1874_);
                    v___y_1857_ = v___x_1872_;
                    v___y_1858_ = v___x_1873_;
                    v___y_1859_ = v_size_1874_;
                    state = 5;
                    continue;
                } else {
                    v___x_1875_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1857_ = v___x_1872_;
                    v___y_1858_ = v___x_1873_;
                    v___y_1859_ = v___x_1875_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1897_ = (!leanh::lean_is_exclusive(v_r_1818_)) as u8;
                if v_isSharedCheck_1897_ == 0 {
                    v_unused_1898_ = leanh::lean_ctor_get(v_r_1818_, 4);
                    leanh::lean_dec(v_unused_1898_);
                    v_unused_1899_ = leanh::lean_ctor_get(v_r_1818_, 3);
                    leanh::lean_dec(v_unused_1899_);
                    v_unused_1900_ = leanh::lean_ctor_get(v_r_1818_, 2);
                    leanh::lean_dec(v_unused_1900_);
                    v_unused_1901_ = leanh::lean_ctor_get(v_r_1818_, 1);
                    leanh::lean_dec(v_unused_1901_);
                    v_unused_1902_ = leanh::lean_ctor_get(v_r_1818_, 0);
                    leanh::lean_dec(v_unused_1902_);
                    v___x_1892_ = v_r_1818_;
                    v_isShared_1893_ = v_isSharedCheck_1897_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_1818_);
                    v___x_1892_ = leanh::lean_box(0);
                    v_isShared_1893_ = v_isSharedCheck_1897_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1893_ == 0 {
                    leanh::lean_ctor_set(v___x_1892_, 4, v___x_1890_);
                    leanh::lean_ctor_set(v___x_1892_, 3, v_l_1829_);
                    leanh::lean_ctor_set(v___x_1892_, 2, v_v_1828_);
                    leanh::lean_ctor_set(v___x_1892_, 1, v_k_1827_);
                    leanh::lean_ctor_set(v___x_1892_, 0, v___x_1886_);
                    v___x_1895_ = v___x_1892_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_k_1827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_v_1828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_l_1829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 4, v___x_1890_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1895_;
            }
            13 => {
                v___x_1917_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_1911_);
                if v_isShared_1916_ == 0 {
                    leanh::lean_ctor_set(v___x_1915_, 3, v_r_1911_);
                    leanh::lean_ctor_set(v___x_1915_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v___x_1915_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v___x_1915_, 0, v___x_1824_);
                    v___x_1919_ = v___x_1915_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1923_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_r_1911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_r_1911_);
                    v___x_1919_ = v_reuseFailAlloc_1923_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 4, v___x_1919_);
                    leanh::lean_ctor_set(v___x_1820_, 3, v_l_1910_);
                    leanh::lean_ctor_set(v___x_1820_, 2, v_v_1913_);
                    leanh::lean_ctor_set(v___x_1820_, 1, v_k_1912_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1917_);
                    v___x_1921_ = v___x_1820_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_l_1910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 4, v___x_1919_);
                    v___x_1921_ = v_reuseFailAlloc_1922_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1921_;
            }
            16 => {
                v_k_1933_ = leanh::lean_ctor_get(v_r_1927_, 1);
                v_v_1934_ = leanh::lean_ctor_get(v_r_1927_, 2);
                v_isSharedCheck_1948_ = (!leanh::lean_is_exclusive(v_r_1927_)) as u8;
                if v_isSharedCheck_1948_ == 0 {
                    v_unused_1949_ = leanh::lean_ctor_get(v_r_1927_, 4);
                    leanh::lean_dec(v_unused_1949_);
                    v_unused_1950_ = leanh::lean_ctor_get(v_r_1927_, 3);
                    leanh::lean_dec(v_unused_1950_);
                    v_unused_1951_ = leanh::lean_ctor_get(v_r_1927_, 0);
                    leanh::lean_dec(v_unused_1951_);
                    v___x_1936_ = v_r_1927_;
                    v_isShared_1937_ = v_isSharedCheck_1948_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1934_);
                    leanh::lean_inc(v_k_1933_);
                    leanh::lean_dec(v_r_1927_);
                    v___x_1936_ = leanh::lean_box(0);
                    v_isShared_1937_ = v_isSharedCheck_1948_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1938_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_1937_ == 0 {
                    leanh::lean_ctor_set(v___x_1936_, 4, v_l_1910_);
                    leanh::lean_ctor_set(v___x_1936_, 3, v_l_1910_);
                    leanh::lean_ctor_set(v___x_1936_, 2, v_v_1929_);
                    leanh::lean_ctor_set(v___x_1936_, 1, v_k_1928_);
                    leanh::lean_ctor_set(v___x_1936_, 0, v___x_1824_);
                    v___x_1940_ = v___x_1936_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1929_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_l_1910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_l_1910_);
                    v___x_1940_ = v_reuseFailAlloc_1947_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1932_ == 0 {
                    leanh::lean_ctor_set(v___x_1931_, 4, v_l_1910_);
                    leanh::lean_ctor_set(v___x_1931_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v___x_1931_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v___x_1931_, 0, v___x_1824_);
                    v___x_1942_ = v___x_1931_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_l_1910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_l_1910_);
                    v___x_1942_ = v_reuseFailAlloc_1946_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 4, v___x_1942_);
                    leanh::lean_ctor_set(v___x_1820_, 3, v___x_1940_);
                    leanh::lean_ctor_set(v___x_1820_, 2, v_v_1934_);
                    leanh::lean_ctor_set(v___x_1820_, 1, v_k_1933_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_1938_);
                    v___x_1944_ = v___x_1820_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_k_1933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_v_1934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 3, v___x_1940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 4, v___x_1942_);
                    v___x_1944_ = v_reuseFailAlloc_1945_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1944_;
            }
            21 => {
                return v___x_1958_;
            }
            22 => {
                return v___x_1961_;
            }
            23 => {
                return v___x_1977_;
            }
            24 => {
                v_size_1982_ = leanh::lean_ctor_get(v_l_1969_, 0);
                v_k_1983_ = leanh::lean_ctor_get(v_l_1969_, 1);
                v_v_1984_ = leanh::lean_ctor_get(v_l_1969_, 2);
                v_l_1985_ = leanh::lean_ctor_get(v_l_1969_, 3);
                v_r_1986_ = leanh::lean_ctor_get(v_l_1969_, 4);
                v_size_1987_ = leanh::lean_ctor_get(v_r_1970_, 0);
                v___x_1988_ = leanh::lean_unsigned_to_nat(2);
                v___x_1989_ = lean_nat_mul(v___x_1988_, v_size_1987_);
                v___x_1990_ = lean_nat_dec_lt(v_size_1982_, v___x_1989_);
                leanh::lean_dec(v___x_1989_);
                if v___x_1990_ == 0 {
                    leanh::lean_inc(v_r_1986_);
                    leanh::lean_inc(v_l_1985_);
                    leanh::lean_inc(v_v_1984_);
                    leanh::lean_inc(v_k_1983_);
                    v_isSharedCheck_2018_ = (!leanh::lean_is_exclusive(v_l_1969_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v_unused_2019_ = leanh::lean_ctor_get(v_l_1969_, 4);
                        leanh::lean_dec(v_unused_2019_);
                        v_unused_2020_ = leanh::lean_ctor_get(v_l_1969_, 3);
                        leanh::lean_dec(v_unused_2020_);
                        v_unused_2021_ = leanh::lean_ctor_get(v_l_1969_, 2);
                        leanh::lean_dec(v_unused_2021_);
                        v_unused_2022_ = leanh::lean_ctor_get(v_l_1969_, 1);
                        leanh::lean_dec(v_unused_2022_);
                        v_unused_2023_ = leanh::lean_ctor_get(v_l_1969_, 0);
                        leanh::lean_dec(v_unused_2023_);
                        v___x_1992_ = v_l_1969_;
                        v_isShared_1993_ = v_isSharedCheck_2018_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_1969_);
                        v___x_1992_ = leanh::lean_box(0);
                        v_isShared_1993_ = v_isSharedCheck_2018_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1820_);
                    v___x_2024_ = lean_nat_add(v___x_1964_, v_size_1965_);
                    v___x_2025_ = lean_nat_add(v___x_2024_, v_size_1966_);
                    leanh::lean_dec(v_size_1966_);
                    v___x_2026_ = lean_nat_add(v___x_2024_, v_size_1982_);
                    leanh::lean_dec(v___x_2024_);
                    leanh::lean_inc_ref(v_l_1817_);
                    if v_isShared_1981_ == 0 {
                        leanh::lean_ctor_set(v___x_1980_, 4, v_l_1969_);
                        leanh::lean_ctor_set(v___x_1980_, 3, v_l_1817_);
                        leanh::lean_ctor_set(v___x_1980_, 2, v_v_1816_);
                        leanh::lean_ctor_set(v___x_1980_, 1, v_k_1815_);
                        leanh::lean_ctor_set(v___x_1980_, 0, v___x_2026_);
                        v___x_2028_ = v___x_1980_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2041_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2026_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1815_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1816_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_l_1817_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_l_1969_);
                        v___x_2028_ = v_reuseFailAlloc_2041_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1994_ = lean_nat_add(v___x_1964_, v_size_1965_);
                v___x_1995_ = lean_nat_add(v___x_1994_, v_size_1966_);
                leanh::lean_dec(v_size_1966_);
                if leanh::lean_obj_tag(v_l_1985_) == 0 {
                    v_size_2016_ = leanh::lean_ctor_get(v_l_1985_, 0);
                    leanh::lean_inc(v_size_2016_);
                    v___y_2008_ = v_size_2016_;
                    state = 29;
                    continue;
                } else {
                    v___x_2017_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2008_ = v___x_2017_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2000_ = lean_nat_add(v___y_1998_, v___y_1999_);
                leanh::lean_dec(v___y_1999_);
                leanh::lean_dec(v___y_1998_);
                if v_isShared_1993_ == 0 {
                    leanh::lean_ctor_set(v___x_1992_, 4, v_r_1970_);
                    leanh::lean_ctor_set(v___x_1992_, 3, v_r_1986_);
                    leanh::lean_ctor_set(v___x_1992_, 2, v_v_1968_);
                    leanh::lean_ctor_set(v___x_1992_, 1, v_k_1967_);
                    leanh::lean_ctor_set(v___x_1992_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1992_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_1968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_r_1986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_r_1970_);
                    v___x_2002_ = v_reuseFailAlloc_2006_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1981_ == 0 {
                    leanh::lean_ctor_set(v___x_1980_, 4, v___x_2002_);
                    leanh::lean_ctor_set(v___x_1980_, 3, v___y_1997_);
                    leanh::lean_ctor_set(v___x_1980_, 2, v_v_1984_);
                    leanh::lean_ctor_set(v___x_1980_, 1, v_k_1983_);
                    leanh::lean_ctor_set(v___x_1980_, 0, v___x_1995_);
                    v___x_2004_ = v___x_1980_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 3, v___y_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 4, v___x_2002_);
                    v___x_2004_ = v_reuseFailAlloc_2005_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2004_;
            }
            29 => {
                v___x_2009_ = lean_nat_add(v___x_1994_, v___y_2008_);
                leanh::lean_dec(v___y_2008_);
                leanh::lean_dec(v___x_1994_);
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 4, v_l_1985_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_2009_);
                    v___x_2011_ = v___x_1820_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_l_1817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_l_1985_);
                    v___x_2011_ = v_reuseFailAlloc_2015_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2012_ = lean_nat_add(v___x_1964_, v_size_1987_);
                if leanh::lean_obj_tag(v_r_1986_) == 0 {
                    v_size_2013_ = leanh::lean_ctor_get(v_r_1986_, 0);
                    leanh::lean_inc(v_size_2013_);
                    v___y_1997_ = v___x_2011_;
                    v___y_1998_ = v___x_2012_;
                    v___y_1999_ = v_size_2013_;
                    state = 26;
                    continue;
                } else {
                    v___x_2014_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1997_ = v___x_2011_;
                    v___y_1998_ = v___x_2012_;
                    v___y_1999_ = v___x_2014_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2035_ = (!leanh::lean_is_exclusive(v_l_1817_)) as u8;
                if v_isSharedCheck_2035_ == 0 {
                    v_unused_2036_ = leanh::lean_ctor_get(v_l_1817_, 4);
                    leanh::lean_dec(v_unused_2036_);
                    v_unused_2037_ = leanh::lean_ctor_get(v_l_1817_, 3);
                    leanh::lean_dec(v_unused_2037_);
                    v_unused_2038_ = leanh::lean_ctor_get(v_l_1817_, 2);
                    leanh::lean_dec(v_unused_2038_);
                    v_unused_2039_ = leanh::lean_ctor_get(v_l_1817_, 1);
                    leanh::lean_dec(v_unused_2039_);
                    v_unused_2040_ = leanh::lean_ctor_get(v_l_1817_, 0);
                    leanh::lean_dec(v_unused_2040_);
                    v___x_2030_ = v_l_1817_;
                    v_isShared_2031_ = v_isSharedCheck_2035_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_1817_);
                    v___x_2030_ = leanh::lean_box(0);
                    v_isShared_2031_ = v_isSharedCheck_2035_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2031_ == 0 {
                    leanh::lean_ctor_set(v___x_2030_, 4, v_r_1970_);
                    leanh::lean_ctor_set(v___x_2030_, 3, v___x_2028_);
                    leanh::lean_ctor_set(v___x_2030_, 2, v_v_1968_);
                    leanh::lean_ctor_set(v___x_2030_, 1, v_k_1967_);
                    leanh::lean_ctor_set(v___x_2030_, 0, v___x_2025_);
                    v___x_2033_ = v___x_2030_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 3, v___x_2028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_r_1970_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2033_;
            }
            34 => {
                v_k_2055_ = leanh::lean_ctor_get(v_l_2048_, 1);
                v_v_2056_ = leanh::lean_ctor_get(v_l_2048_, 2);
                v_isSharedCheck_2070_ = (!leanh::lean_is_exclusive(v_l_2048_)) as u8;
                if v_isSharedCheck_2070_ == 0 {
                    v_unused_2071_ = leanh::lean_ctor_get(v_l_2048_, 4);
                    leanh::lean_dec(v_unused_2071_);
                    v_unused_2072_ = leanh::lean_ctor_get(v_l_2048_, 3);
                    leanh::lean_dec(v_unused_2072_);
                    v_unused_2073_ = leanh::lean_ctor_get(v_l_2048_, 0);
                    leanh::lean_dec(v_unused_2073_);
                    v___x_2058_ = v_l_2048_;
                    v_isShared_2059_ = v_isSharedCheck_2070_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2056_);
                    leanh::lean_inc(v_k_2055_);
                    leanh::lean_dec(v_l_2048_);
                    v___x_2058_ = leanh::lean_box(0);
                    v_isShared_2059_ = v_isSharedCheck_2070_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2060_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_2049_, 2);
                if v_isShared_2059_ == 0 {
                    leanh::lean_ctor_set(v___x_2058_, 4, v_r_2049_);
                    leanh::lean_ctor_set(v___x_2058_, 3, v_r_2049_);
                    leanh::lean_ctor_set(v___x_2058_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v___x_2058_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v___x_2058_, 0, v___x_1964_);
                    v___x_2062_ = v___x_2058_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_r_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_r_2049_);
                    v___x_2062_ = v_reuseFailAlloc_2069_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_2049_);
                if v_isShared_2054_ == 0 {
                    leanh::lean_ctor_set(v___x_2053_, 3, v_r_2049_);
                    leanh::lean_ctor_set(v___x_2053_, 0, v___x_1964_);
                    v___x_2064_ = v___x_2053_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_2051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_r_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_r_2049_);
                    v___x_2064_ = v_reuseFailAlloc_2068_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 4, v___x_2064_);
                    leanh::lean_ctor_set(v___x_1820_, 3, v___x_2062_);
                    leanh::lean_ctor_set(v___x_1820_, 2, v_v_2056_);
                    leanh::lean_ctor_set(v___x_1820_, 1, v_k_2055_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_2060_);
                    v___x_2066_ = v___x_1820_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 3, v___x_2062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 4, v___x_2064_);
                    v___x_2066_ = v_reuseFailAlloc_2067_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2066_;
            }
            39 => {
                v___x_2083_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_2082_ == 0 {
                    leanh::lean_ctor_set(v___x_2081_, 4, v_l_2048_);
                    leanh::lean_ctor_set(v___x_2081_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v___x_2081_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v___x_2081_, 0, v___x_1964_);
                    v___x_2085_ = v___x_2081_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_k_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_v_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_l_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_l_2048_);
                    v___x_2085_ = v_reuseFailAlloc_2089_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 4, v_r_2077_);
                    leanh::lean_ctor_set(v___x_1820_, 3, v___x_2085_);
                    leanh::lean_ctor_set(v___x_1820_, 2, v_v_2079_);
                    leanh::lean_ctor_set(v___x_1820_, 1, v_k_2078_);
                    leanh::lean_ctor_set(v___x_1820_, 0, v___x_2083_);
                    v___x_2087_ = v___x_1820_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_2078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_2079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 3, v___x_2085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_r_2077_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2087_;
            }
            42 => {
                return v___x_2096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(
    mut v_init_2101_: *mut leanh::LeanObject,
    mut v_x_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2102_) == 0 {
                    v_k_2103_ = leanh::lean_ctor_get(v_x_2102_, 1);
                    leanh::lean_inc(v_k_2103_);
                    v_v_2104_ = leanh::lean_ctor_get(v_x_2102_, 2);
                    leanh::lean_inc(v_v_2104_);
                    v_l_2105_ = leanh::lean_ctor_get(v_x_2102_, 3);
                    leanh::lean_inc(v_l_2105_);
                    v_r_2106_ = leanh::lean_ctor_get(v_x_2102_, 4);
                    leanh::lean_inc(v_r_2106_);
                    leanh::lean_dec_ref_known(v_x_2102_, 5);
                    v___x_2107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_init_2101_, v_l_2105_);
                    if leanh::lean_obj_tag(v___x_2107_) == 0 {
                        leanh::lean_dec(v_r_2106_);
                        leanh::lean_dec(v_v_2104_);
                        leanh::lean_dec(v_k_2103_);
                        return v___x_2107_;
                    } else {
                        v_val_2108_ = leanh::lean_ctor_get(v___x_2107_, 0);
                        leanh::lean_inc(v_val_2108_);
                        leanh::lean_dec_ref_known(v___x_2107_, 1);
                        v_a_2109_ = leanh::lean_ctor_get(v_val_2108_, 0);
                        leanh::lean_inc(v_a_2109_);
                        leanh::lean_dec(v_val_2108_);
                        v___x_2110_ = l_Lean_LeanOptionValue_ofDataValue_x3f(v_v_2104_);
                        if leanh::lean_obj_tag(v___x_2110_) == 0 {
                            leanh::lean_dec(v_a_2109_);
                            leanh::lean_dec(v_r_2106_);
                            leanh::lean_dec(v_k_2103_);
                            v___x_2111_ = leanh::lean_box(0);
                            return v___x_2111_;
                        } else {
                            v_val_2112_ = leanh::lean_ctor_get(v___x_2110_, 0);
                            leanh::lean_inc(v_val_2112_);
                            leanh::lean_dec_ref_known(v___x_2110_, 1);
                            v___x_2113_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_2103_, v_val_2112_, v_a_2109_);
                            v_init_2101_ = v___x_2113_;
                            v_x_2102_ = v_r_2106_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2115_, 0, v_init_2101_);
                    v___x_2116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2116_, 0, v___x_2115_);
                    return v___x_2116_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_fromOptions_x3f(
    mut v_options_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v_a_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2118_ = leanh::lean_ctor_get(v_options_2117_, 0);
                leanh::lean_inc(v_map_2118_);
                leanh::lean_dec_ref(v_options_2117_);
                v_values_2119_ = leanh::lean_box(1);
                v___x_2120_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_values_2119_, v_map_2118_);
                if leanh::lean_obj_tag(v___x_2120_) == 0 {
                    v___x_2121_ = leanh::lean_box(0);
                    return v___x_2121_;
                } else {
                    v_val_2122_ = leanh::lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2130_ = (!leanh::lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2130_ == 0 {
                        v___x_2124_ = v___x_2120_;
                        v_isShared_2125_ = v_isSharedCheck_2130_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2122_);
                        leanh::lean_dec(v___x_2120_);
                        v___x_2124_ = leanh::lean_box(0);
                        v_isShared_2125_ = v_isSharedCheck_2130_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2126_ = leanh::lean_ctor_get(v_val_2122_, 0);
                leanh::lean_inc(v_a_2126_);
                leanh::lean_dec(v_val_2122_);
                if v_isShared_2125_ == 0 {
                    leanh::lean_ctor_set(v___x_2124_, 0, v_a_2126_);
                    v___x_2128_ = v___x_2124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2126_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0(
    mut v_00_u03b2_2131_: *mut leanh::LeanObject,
    mut v_k_2132_: *mut leanh::LeanObject,
    mut v_v_2133_: *mut leanh::LeanObject,
    mut v_t_2134_: *mut leanh::LeanObject,
    mut v_hl_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_2132_, v_v_2133_, v_t_2134_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_instFromJsonLeanOptions___lam__0(
    mut v___f_2137_: *mut leanh::LeanObject,
    mut v_j_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_a_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2151_: u8 = 0;
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = l_Lean_NameMap_fromJson_x3f___redArg(v___f_2137_, v_j_2138_);
                if leanh::lean_obj_tag(v___x_2139_) == 0 {
                    v_a_2140_ = leanh::lean_ctor_get(v___x_2139_, 0);
                    v_isSharedCheck_2147_ = (!leanh::lean_is_exclusive(v___x_2139_)) as u8;
                    if v_isSharedCheck_2147_ == 0 {
                        v___x_2142_ = v___x_2139_;
                        v_isShared_2143_ = v_isSharedCheck_2147_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2140_);
                        leanh::lean_dec(v___x_2139_);
                        v___x_2142_ = leanh::lean_box(0);
                        v_isShared_2143_ = v_isSharedCheck_2147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2148_ = leanh::lean_ctor_get(v___x_2139_, 0);
                    v_isSharedCheck_2155_ = (!leanh::lean_is_exclusive(v___x_2139_)) as u8;
                    if v_isSharedCheck_2155_ == 0 {
                        v___x_2150_ = v___x_2139_;
                        v_isShared_2151_ = v_isSharedCheck_2155_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2148_);
                        leanh::lean_dec(v___x_2139_);
                        v___x_2150_ = leanh::lean_box(0);
                        v_isShared_2151_ = v_isSharedCheck_2155_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2143_ == 0 {
                    v___x_2145_ = v___x_2142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
                    v___x_2145_ = v_reuseFailAlloc_2146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2145_;
            }
            3 => {
                if v_isShared_2151_ == 0 {
                    v___x_2153_ = v___x_2150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonLeanOptions___lam__0(
    mut v___f_2159_: *mut leanh::LeanObject,
    mut v_options_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_NameMap_toJson___redArg(v___f_2159_, v_options_2160_);
    return v___x_2161_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_LeanOptions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedLeanOptions_default = _init_l_Lean_instInhabitedLeanOptions_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLeanOptions_default);
    l_Lean_instInhabitedLeanOptions = _init_l_Lean_instInhabitedLeanOptions();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLeanOptions);
    l_Lean_instEmptyCollectionLeanOptions = _init_l_Lean_instEmptyCollectionLeanOptions();
    leanh::lean_mark_persistent(l_Lean_instEmptyCollectionLeanOptions);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_LeanOptions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_LeanOptions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_LeanOptions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_LeanOptions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_LeanOptions(builtin);
}