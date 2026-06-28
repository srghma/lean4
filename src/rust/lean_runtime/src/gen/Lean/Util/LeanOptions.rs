// Lean compiler output
// Module: Lean.Util.LeanOptions
// Imports: Lean.Data.Json.FromToJson.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen, l_String_quote,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_usize_dec_eq,
};
pub static l_Lean_instInhabitedLeanOptionValue_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l_Lean_instInhabitedLeanOptionValue_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedLeanOptionValue_default___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedLeanOptionValue_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOptionValue_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__0_value: crate::leanh::LeanStringObject<
    30,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLeanOptionValue_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLeanOptionValue_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLeanOptionValue_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOptionValue_repr___closed__5_value: crate::leanh::LeanStringObject<
    28,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLeanOptionValue_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__8_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLeanOptionValue_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue_repr___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLeanOptionValue_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLeanOptionValue_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instValueLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LeanOptionValue_toDataValue as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instValueLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instValueLeanOptionValue___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LeanOptionValue_ofDataValue_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instValueLeanOptionValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instValueLeanOptionValue___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instValueLeanOptionValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instValueLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instValueLeanOptionValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instCoeStringLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_instCoeStringLeanOptionValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instCoeStringLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instCoeStringLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instCoeBoolLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeBoolLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instCoeBoolLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instCoeNatLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeNatLeanOptionValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeNatLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instCoeNatLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_instFromJsonLeanOptionValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instFromJsonLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToJsonLeanOptionValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonLeanOptionValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonLeanOptionValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instToJsonLeanOptionValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptionValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_LeanOptionValue_asCliFlagValue___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [34, 0],
};
static mut l_Lean_LeanOptionValue_asCliFlagValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOptionValue_asCliFlagValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_LeanOptionValue_asCliFlagValue___closed__1_value: crate::leanh::LeanStringObject<
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
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_LeanOptionValue_asCliFlagValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOptionValue_asCliFlagValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_LeanOptionValue_asCliFlagValue___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_LeanOptionValue_asCliFlagValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOptionValue_asCliFlagValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedLeanOption_default___closed__0_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedLeanOptionValue_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedLeanOption_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOption_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOption_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOption_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedLeanOption_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__0_value:
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
static mut l_Lean_instReprLeanOption_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__1_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__4_value:
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
static mut l_Lean_instReprLeanOption_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLeanOption_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOption_repr___redArg___closed__8_value:
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
static mut l_Lean_instReprLeanOption_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__10_value:
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
    m_data: [118, 97, 108, 117, 101, 0],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLeanOption_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOption_repr___redArg___closed__13_value:
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
static mut l_Lean_instReprLeanOption_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLeanOption_repr___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLeanOption_repr___redArg___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOption_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOption_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption_repr___redArg___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOption_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOption___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLeanOption_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLeanOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprLeanOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_LeanOption_asCliArg___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [45, 68, 0],
    };
static mut l_Lean_LeanOption_asCliArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOption_asCliArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_LeanOption_asCliArg___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [61, 0],
    };
static mut l_Lean_LeanOption_asCliArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LeanOption_asCliArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLeanOptions_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLeanOptions: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__9_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value:
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
    m_data: [91, 93, 0],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1_value:
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
        l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value:
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
    m_data: [91, 0],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value:
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
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6_value:
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
        l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7_value:
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
        l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__0_value:
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
    m_data: [118, 97, 108, 117, 101, 115, 0],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLeanOption_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptions_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLeanOptions_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLeanOptions___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLeanOptions_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLeanOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprLeanOptions: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instEmptyCollectionLeanOptions: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instAppendLeanOptions___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LeanOptions_append as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instAppendLeanOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instAppendLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instAppendLeanOptions: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instAppendLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value:
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
    m_fun: l_Lean_LeanOptions_appendArray___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instHAppendLeanOptionsArrayLeanOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHAppendLeanOptionsArrayLeanOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instFromJsonLeanOptions___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_instFromJsonLeanOptions___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonLeanOptionValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instFromJsonLeanOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instFromJsonLeanOptions: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToJsonLeanOptions___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_instToJsonLeanOptions___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_instToJsonLeanOptionValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instToJsonLeanOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instToJsonLeanOptions: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonLeanOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_LeanOptionValue_ctorIdx(
    mut v_x_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1083_) {
        0 => {
            let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1084_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1084_;
        }
        1 => {
            let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1085_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1085_;
        }
        _ => {
            let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1086_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1086_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_ctorIdx___boxed(
    mut v_x_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_Lean_LeanOptionValue_ctorIdx(v_x_1087_);
    crate::leanh::lean_dec_ref(v_x_1087_);
    return v_res_1088_;
}
pub unsafe fn l_Lean_LeanOptionValue_ctorElim___redArg(
    mut v_t_1089_: *mut crate::leanh::LeanObject,
    mut v_k_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1089_) {
        0 => {
            let mut v_s_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_s_1091_ = crate::leanh::lean_ctor_get(v_t_1089_, 0);
            crate::leanh::lean_inc_ref(v_s_1091_);
            crate::leanh::lean_dec_ref_known(v_t_1089_, 1);
            v___x_1092_ = crate::leanh::lean_apply_1(v_k_1090_, v_s_1091_);
            return v___x_1092_;
        }
        1 => {
            let mut v_b_1093_: u8 = 0;
            let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_1093_ = crate::leanh::lean_ctor_get_uint8(v_t_1089_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_t_1089_, 0);
            v___x_1094_ = crate::leanh::lean_box((v_b_1093_) as usize);
            v___x_1095_ = crate::leanh::lean_apply_1(v_k_1090_, v___x_1094_);
            return v___x_1095_;
        }
        _ => {
            let mut v_n_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_1096_ = crate::leanh::lean_ctor_get(v_t_1089_, 0);
            crate::leanh::lean_inc(v_n_1096_);
            crate::leanh::lean_dec_ref_known(v_t_1089_, 1);
            v___x_1097_ = crate::leanh::lean_apply_1(v_k_1090_, v_n_1096_);
            return v___x_1097_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_ctorElim(
    mut v_motive_1098_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1099_: *mut crate::leanh::LeanObject,
    mut v_t_1100_: *mut crate::leanh::LeanObject,
    mut v_h_1101_: *mut crate::leanh::LeanObject,
    mut v_k_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1103_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1100_, v_k_1102_);
    return v___x_1103_;
}
pub unsafe fn l_Lean_LeanOptionValue_ctorElim___boxed(
    mut v_motive_1104_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1105_: *mut crate::leanh::LeanObject,
    mut v_t_1106_: *mut crate::leanh::LeanObject,
    mut v_h_1107_: *mut crate::leanh::LeanObject,
    mut v_k_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_LeanOptionValue_ctorElim(
        v_motive_1104_,
        v_ctorIdx_1105_,
        v_t_1106_,
        v_h_1107_,
        v_k_1108_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1105_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofString_elim___redArg(
    mut v_t_1110_: *mut crate::leanh::LeanObject,
    mut v_ofString_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1110_, v_ofString_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofString_elim(
    mut v_motive_1113_: *mut crate::leanh::LeanObject,
    mut v_t_1114_: *mut crate::leanh::LeanObject,
    mut v_h_1115_: *mut crate::leanh::LeanObject,
    mut v_ofString_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1114_, v_ofString_1116_);
    return v___x_1117_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofBool_elim___redArg(
    mut v_t_1118_: *mut crate::leanh::LeanObject,
    mut v_ofBool_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1118_, v_ofBool_1119_);
    return v___x_1120_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofBool_elim(
    mut v_motive_1121_: *mut crate::leanh::LeanObject,
    mut v_t_1122_: *mut crate::leanh::LeanObject,
    mut v_h_1123_: *mut crate::leanh::LeanObject,
    mut v_ofBool_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1122_, v_ofBool_1124_);
    return v___x_1125_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofNat_elim___redArg(
    mut v_t_1126_: *mut crate::leanh::LeanObject,
    mut v_ofNat_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1126_, v_ofNat_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofNat_elim(
    mut v_motive_1129_: *mut crate::leanh::LeanObject,
    mut v_t_1130_: *mut crate::leanh::LeanObject,
    mut v_h_1131_: *mut crate::leanh::LeanObject,
    mut v_ofNat_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = l_Lean_LeanOptionValue_ctorElim___redArg(v_t_1130_, v_ofNat_1132_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lean_instReprLeanOptionValue_repr___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1146_ = lean_nat_to_int(v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn _init_l_Lean_instReprLeanOptionValue_repr___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1147_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1148_ = lean_nat_to_int(v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_instReprLeanOptionValue_repr(
    mut v_x_1161_: *mut crate::leanh::LeanObject,
    mut v_prec_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___y_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1183_: u8 = 0;
    let mut v_b_1184_: u8 = 0;
    let mut v___y_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___y_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1161_) {
                0 => {
                    v_s_1163_ = crate::leanh::lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1183_ = (!crate::leanh::lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1183_ == 0 {
                        v___x_1165_ = v_x_1161_;
                        v_isShared_1166_ = v_isSharedCheck_1183_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_1163_);
                        crate::leanh::lean_dec(v_x_1161_);
                        v___x_1165_ = crate::leanh::lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1183_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_b_1184_ = crate::leanh::lean_ctor_get_uint8(v_x_1161_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_x_1161_, 0);
                    v___x_1194_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1195_ = lean_nat_dec_le(v___x_1194_, v_prec_1162_);
                    if v___x_1195_ == 0 {
                        v___x_1196_ = crate::leanh::lean_obj_once(
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
                        v___x_1197_ = crate::leanh::lean_obj_once(
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
                    v_n_1198_ = crate::leanh::lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1218_ = (!crate::leanh::lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1218_ == 0 {
                        v___x_1200_ = v_x_1161_;
                        v_isShared_1201_ = v_isSharedCheck_1218_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_1198_);
                        crate::leanh::lean_dec(v_x_1161_);
                        v___x_1200_ = crate::leanh::lean_box(0);
                        v_isShared_1201_ = v_isSharedCheck_1218_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1179_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1180_ = lean_nat_dec_le(v___x_1179_, v_prec_1162_);
                if v___x_1180_ == 0 {
                    v___x_1181_ = crate::leanh::lean_obj_once(
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
                    v___x_1182_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_1165_, 3);
                    crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1170_);
                    v___x_1172_ = v___x_1165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1178_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1170_);
                    v___x_1172_ = v_reuseFailAlloc_1178_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1173_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1169_);
                crate::leanh::lean_ctor_set(v___x_1173_, 1, v___x_1172_);
                crate::leanh::lean_inc(v___y_1168_);
                v___x_1174_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1174_, 0, v___y_1168_);
                crate::leanh::lean_ctor_set(v___x_1174_, 1, v___x_1173_);
                v___x_1175_ = 0;
                v___x_1176_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1174_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1176_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1175_,
                );
                v___x_1177_ = l_Repr_addAppParen(v___x_1176_, v_prec_1162_);
                return v___x_1177_;
            }
            4 => {
                v___x_1187_ = l_Lean_instReprLeanOptionValue_repr___closed__7;
                v___x_1188_ = l_Bool_repr___redArg(v_b_1184_);
                v___x_1189_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1189_, 0, v___x_1187_);
                crate::leanh::lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                crate::leanh::lean_inc(v___y_1186_);
                v___x_1190_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1190_, 0, v___y_1186_);
                crate::leanh::lean_ctor_set(v___x_1190_, 1, v___x_1189_);
                v___x_1191_ = 0;
                v___x_1192_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1190_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1192_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1191_,
                );
                v___x_1193_ = l_Repr_addAppParen(v___x_1192_, v_prec_1162_);
                return v___x_1193_;
            }
            5 => {
                v___x_1214_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1215_ = lean_nat_dec_le(v___x_1214_, v_prec_1162_);
                if v___x_1215_ == 0 {
                    v___x_1216_ = crate::leanh::lean_obj_once(
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
                    v___x_1217_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set_tag(v___x_1200_, 3);
                    crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1205_);
                    v___x_1207_ = v___x_1200_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1205_);
                    v___x_1207_ = v_reuseFailAlloc_1213_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1208_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1208_, 0, v___x_1204_);
                crate::leanh::lean_ctor_set(v___x_1208_, 1, v___x_1207_);
                crate::leanh::lean_inc(v___y_1203_);
                v___x_1209_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1209_, 0, v___y_1203_);
                crate::leanh::lean_ctor_set(v___x_1209_, 1, v___x_1208_);
                v___x_1210_ = 0;
                v___x_1211_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1211_, 0, v___x_1209_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1211_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_1219_: *mut crate::leanh::LeanObject,
    mut v_prec_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Lean_instReprLeanOptionValue_repr(v_x_1219_, v_prec_1220_);
    crate::leanh::lean_dec(v_prec_1220_);
    return v_res_1221_;
}
pub unsafe fn l_Lean_LeanOptionValue_ofDataValue_x3f(
    mut v_x_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1228_: u8 = 0;
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut v_v_1234_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1242_: u8 = 0;
    let mut v_v_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1224_) {
                0 => {
                    v_v_1225_ = crate::leanh::lean_ctor_get(v_x_1224_, 0);
                    v_isSharedCheck_1233_ = (!crate::leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1227_ = v_x_1224_;
                        v_isShared_1228_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_1225_);
                        crate::leanh::lean_dec(v_x_1224_);
                        v___x_1227_ = crate::leanh::lean_box(0);
                        v_isShared_1228_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_v_1234_ = crate::leanh::lean_ctor_get_uint8(v_x_1224_, 0 as u32);
                    v_isSharedCheck_1242_ = (!crate::leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1242_ == 0 {
                        v___x_1236_ = v_x_1224_;
                        v_isShared_1237_ = v_isSharedCheck_1242_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1224_);
                        v___x_1236_ = crate::leanh::lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1242_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_v_1243_ = crate::leanh::lean_ctor_get(v_x_1224_, 0);
                    v_isSharedCheck_1251_ = (!crate::leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v___x_1245_ = v_x_1224_;
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_1243_);
                        crate::leanh::lean_dec(v_x_1224_);
                        v___x_1245_ = crate::leanh::lean_box(0);
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_1224_);
                    v___x_1252_ = crate::leanh::lean_box(0);
                    return v___x_1252_;
                }
            },
            1 => {
                if v_isShared_1228_ == 0 {
                    v___x_1230_ = v___x_1227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_v_1225_);
                    v___x_1230_ = v_reuseFailAlloc_1232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1231_, 0, v___x_1230_);
                return v___x_1231_;
            }
            3 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1241_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1241_, 0 as u32, v_v_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1240_, 0, v___x_1239_);
                return v___x_1240_;
            }
            5 => {
                if v_isShared_1246_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1245_, 2);
                    v___x_1248_ = v___x_1245_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_v_1243_);
                    v___x_1248_ = v_reuseFailAlloc_1250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1248_);
                return v___x_1249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptionValue_toDataValue(
    mut v_x_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_b_1262_: u8 = 0;
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1269_: u8 = 0;
    let mut v_n_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1273_: u8 = 0;
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1253_) {
                0 => {
                    v_s_1254_ = crate::leanh::lean_ctor_get(v_x_1253_, 0);
                    v_isSharedCheck_1261_ = (!crate::leanh::lean_is_exclusive(v_x_1253_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1256_ = v_x_1253_;
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_1254_);
                        crate::leanh::lean_dec(v_x_1253_);
                        v___x_1256_ = crate::leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_b_1262_ = crate::leanh::lean_ctor_get_uint8(v_x_1253_, 0 as u32);
                    v_isSharedCheck_1269_ = (!crate::leanh::lean_is_exclusive(v_x_1253_)) as u8;
                    if v_isSharedCheck_1269_ == 0 {
                        v___x_1264_ = v_x_1253_;
                        v_isShared_1265_ = v_isSharedCheck_1269_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1253_);
                        v___x_1264_ = crate::leanh::lean_box(0);
                        v_isShared_1265_ = v_isSharedCheck_1269_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_n_1270_ = crate::leanh::lean_ctor_get(v_x_1253_, 0);
                    v_isSharedCheck_1277_ = (!crate::leanh::lean_is_exclusive(v_x_1253_)) as u8;
                    if v_isSharedCheck_1277_ == 0 {
                        v___x_1272_ = v_x_1253_;
                        v_isShared_1273_ = v_isSharedCheck_1277_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_1270_);
                        crate::leanh::lean_dec(v_x_1253_);
                        v___x_1272_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_s_1254_);
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
                    v_reuseFailAlloc_1268_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1268_, 0 as u32, v_b_1262_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1272_, 3);
                    v___x_1275_ = v___x_1272_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_n_1270_);
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
    mut v_s_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1285_, 0, v_s_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_instCoeBoolLeanOptionValue___lam__0(
    mut v_b_1288_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_1289_, 0 as u32, v_b_1288_);
    return v___x_1289_;
}
pub unsafe fn l_Lean_instCoeBoolLeanOptionValue___lam__0___boxed(
    mut v_b_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1291_: u8 = 0;
    let mut v_res_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1291_ = (crate::leanh::lean_unbox(v_b_1290_) as u8);
    v_res_1292_ = l_Lean_instCoeBoolLeanOptionValue___lam__0(v_b_boxed_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_instCoeNatLeanOptionValue___lam__0(
    mut v_n_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1296_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1296_, 0, v_n_1295_);
    return v___x_1296_;
}
pub unsafe fn l_Lean_instOfNatLeanOptionValue(
    mut v_n_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1300_, 0, v_n_1299_);
    return v___x_1300_;
}
pub unsafe fn _init_l_Lean_instFromJsonLeanOptionValue___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_natZero_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_1304_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_1305_ = lean_nat_to_int(v_natZero_1304_);
    return v_intZero_1305_;
}
pub unsafe fn l_Lean_instFromJsonLeanOptionValue___lam__0(
    mut v_x_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1317_: u8 = 0;
    let mut v_b_1318_: u8 = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_n_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v_mantissa_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1335_: u8 = 0;
    let mut v___x_1336_: u8 = 0;
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1306_) {
                3 => {
                    v_s_1309_ = crate::leanh::lean_ctor_get(v_x_1306_, 0);
                    v_isSharedCheck_1317_ = (!crate::leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1317_ == 0 {
                        v___x_1311_ = v_x_1306_;
                        v_isShared_1312_ = v_isSharedCheck_1317_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_1309_);
                        crate::leanh::lean_dec(v_x_1306_);
                        v___x_1311_ = crate::leanh::lean_box(0);
                        v_isShared_1312_ = v_isSharedCheck_1317_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_b_1318_ = crate::leanh::lean_ctor_get_uint8(v_x_1306_, 0 as u32);
                    v_isSharedCheck_1326_ = (!crate::leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1320_ = v_x_1306_;
                        v_isShared_1321_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1306_);
                        v___x_1320_ = crate::leanh::lean_box(0);
                        v_isShared_1321_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_n_1327_ = crate::leanh::lean_ctor_get(v_x_1306_, 0);
                    v_isSharedCheck_1342_ = (!crate::leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v___x_1329_ = v_x_1306_;
                        v_isShared_1330_ = v_isSharedCheck_1342_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_1327_);
                        crate::leanh::lean_dec(v_x_1306_);
                        v___x_1329_ = crate::leanh::lean_box(0);
                        v_isShared_1330_ = v_isSharedCheck_1342_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_1306_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_1311_, 0);
                    v___x_1314_ = v___x_1311_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1316_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_s_1309_);
                    v___x_1314_ = v_reuseFailAlloc_1316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1315_, 0, v___x_1314_);
                return v___x_1315_;
            }
            4 => {
                if v_isShared_1321_ == 0 {
                    v___x_1323_ = v___x_1320_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1325_, 0 as u32, v_b_1318_);
                    v___x_1323_ = v_reuseFailAlloc_1325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                return v___x_1324_;
            }
            6 => {
                v_mantissa_1331_ = crate::leanh::lean_ctor_get(v_n_1327_, 0);
                crate::leanh::lean_inc(v_mantissa_1331_);
                v_exponent_1332_ = crate::leanh::lean_ctor_get(v_n_1327_, 1);
                crate::leanh::lean_inc(v_exponent_1332_);
                crate::leanh::lean_dec_ref(v_n_1327_);
                v_natZero_1333_ = crate::leanh::lean_unsigned_to_nat(0);
                v_intZero_1334_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v_exponent_1332_);
                    if v___x_1336_ == 0 {
                        crate::leanh::lean_dec(v_mantissa_1331_);
                        crate::leanh::lean_del_object(v___x_1329_);
                        state = 1;
                        continue;
                    } else {
                        v_a_1337_ = lean_nat_abs(v_mantissa_1331_);
                        crate::leanh::lean_dec(v_mantissa_1331_);
                        if v_isShared_1330_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1329_, 0, v_a_1337_);
                            v___x_1339_ = v___x_1329_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1341_ =
                                crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1337_);
                            v___x_1339_ = v_reuseFailAlloc_1341_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_exponent_1332_);
                    crate::leanh::lean_dec(v_mantissa_1331_);
                    crate::leanh::lean_del_object(v___x_1329_);
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_1340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1340_, 0, v___x_1339_);
                return v___x_1340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonLeanOptionValue___lam__0(
    mut v_x_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_b_1354_: u8 = 0;
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_n_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1365_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1345_) {
                0 => {
                    v_s_1346_ = crate::leanh::lean_ctor_get(v_x_1345_, 0);
                    v_isSharedCheck_1353_ = (!crate::leanh::lean_is_exclusive(v_x_1345_)) as u8;
                    if v_isSharedCheck_1353_ == 0 {
                        v___x_1348_ = v_x_1345_;
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_1346_);
                        crate::leanh::lean_dec(v_x_1345_);
                        v___x_1348_ = crate::leanh::lean_box(0);
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_b_1354_ = crate::leanh::lean_ctor_get_uint8(v_x_1345_, 0 as u32);
                    v_isSharedCheck_1361_ = (!crate::leanh::lean_is_exclusive(v_x_1345_)) as u8;
                    if v_isSharedCheck_1361_ == 0 {
                        v___x_1356_ = v_x_1345_;
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1345_);
                        v___x_1356_ = crate::leanh::lean_box(0);
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_n_1362_ = crate::leanh::lean_ctor_get(v_x_1345_, 0);
                    v_isSharedCheck_1370_ = (!crate::leanh::lean_is_exclusive(v_x_1345_)) as u8;
                    if v_isSharedCheck_1370_ == 0 {
                        v___x_1364_ = v_x_1345_;
                        v_isShared_1365_ = v_isSharedCheck_1370_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_1362_);
                        crate::leanh::lean_dec(v_x_1345_);
                        v___x_1364_ = crate::leanh::lean_box(0);
                        v_isShared_1365_ = v_isSharedCheck_1370_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_1349_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1348_, 3);
                    v___x_1351_ = v___x_1348_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_s_1346_);
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
                    v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                    crate::leanh::lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 0 as u32, v_b_1354_);
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
                    crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1366_);
                    v___x_1368_ = v___x_1364_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
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
    mut v_x_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1376_) {
        0 => {
            let mut v_s_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_s_1377_ = crate::leanh::lean_ctor_get(v_x_1376_, 0);
            crate::leanh::lean_inc_ref(v_s_1377_);
            crate::leanh::lean_dec_ref_known(v_x_1376_, 1);
            v___x_1378_ = l_Lean_LeanOptionValue_asCliFlagValue___closed__0;
            v___x_1379_ = lean_string_append(v___x_1378_, v_s_1377_);
            crate::leanh::lean_dec_ref(v_s_1377_);
            v___x_1380_ = lean_string_append(v___x_1379_, v___x_1378_);
            return v___x_1380_;
        }
        1 => {
            let mut v_b_1381_: u8 = 0;
            v_b_1381_ = crate::leanh::lean_ctor_get_uint8(v_x_1376_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_x_1376_, 0);
            if v_b_1381_ == 0 {
                let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1382_ = l_Lean_LeanOptionValue_asCliFlagValue___closed__1;
                return v___x_1382_;
            } else {
                let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1383_ = l_Lean_LeanOptionValue_asCliFlagValue___closed__2;
                return v___x_1383_;
            }
        }
        _ => {
            let mut v_n_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_1384_ = crate::leanh::lean_ctor_get(v_x_1376_, 0);
            crate::leanh::lean_inc(v_n_1384_);
            crate::leanh::lean_dec_ref_known(v_x_1376_, 1);
            v___x_1385_ = l_Nat_reprFast(v_n_1384_);
            return v___x_1385_;
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprLeanOption_repr_spec__0(
    mut v_a_1391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = lean_nat_to_int(v_a_1391_);
    return v___x_1392_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_1407_ = lean_nat_to_int(v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1415_ = lean_nat_to_int(v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_instReprLeanOption_repr___redArg___closed__0;
    v___x_1418_ = lean_string_length(v___x_1417_);
    return v___x_1418_;
}
pub unsafe fn _init_l_Lean_instReprLeanOption_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__14_once),
        _init_l_Lean_instReprLeanOption_repr___redArg___closed__14,
    );
    v___x_1420_ = lean_nat_to_int(v___x_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Lean_instReprLeanOption_repr___redArg(
    mut v_x_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1426_ = crate::leanh::lean_ctor_get(v_x_1425_, 0);
                v_value_1427_ = crate::leanh::lean_ctor_get(v_x_1425_, 1);
                v_isSharedCheck_1461_ = (!crate::leanh::lean_is_exclusive(v_x_1425_)) as u8;
                if v_isSharedCheck_1461_ == 0 {
                    v___x_1429_ = v_x_1425_;
                    v_isShared_1430_ = v_isSharedCheck_1461_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_1427_);
                    crate::leanh::lean_inc(v_name_1426_);
                    crate::leanh::lean_dec(v_x_1425_);
                    v___x_1429_ = crate::leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1461_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1431_ = l_Lean_instReprLeanOption_repr___redArg___closed__5;
                v___x_1432_ = l_Lean_instReprLeanOption_repr___redArg___closed__6;
                v___x_1433_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprLeanOption_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_instReprLeanOption_repr___redArg___closed__7,
                );
                v___x_1434_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1435_ = l_Lean_Name_reprPrec(v_name_1426_, v___x_1434_);
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1429_, 4);
                    crate::leanh::lean_ctor_set(v___x_1429_, 1, v___x_1435_);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v___x_1433_);
                    v___x_1437_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1460_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1435_);
                    v___x_1437_ = v_reuseFailAlloc_1460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1438_ = 0;
                v___x_1439_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1437_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1439_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1438_,
                );
                v___x_1440_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1432_);
                crate::leanh::lean_ctor_set(v___x_1440_, 1, v___x_1439_);
                v___x_1441_ = l_Lean_instReprLeanOption_repr___redArg___closed__9;
                v___x_1442_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1442_, 0, v___x_1440_);
                crate::leanh::lean_ctor_set(v___x_1442_, 1, v___x_1441_);
                v___x_1443_ = crate::leanh::lean_box(1);
                v___x_1444_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1442_);
                crate::leanh::lean_ctor_set(v___x_1444_, 1, v___x_1443_);
                v___x_1445_ = l_Lean_instReprLeanOption_repr___redArg___closed__11;
                v___x_1446_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1444_);
                crate::leanh::lean_ctor_set(v___x_1446_, 1, v___x_1445_);
                v___x_1447_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1446_);
                crate::leanh::lean_ctor_set(v___x_1447_, 1, v___x_1431_);
                v___x_1448_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprLeanOption_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_instReprLeanOption_repr___redArg___closed__12,
                );
                v___x_1449_ = l_Lean_instReprLeanOptionValue_repr(v_value_1427_, v___x_1434_);
                v___x_1450_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1450_, 0, v___x_1448_);
                crate::leanh::lean_ctor_set(v___x_1450_, 1, v___x_1449_);
                v___x_1451_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1451_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1438_,
                );
                v___x_1452_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1452_, 0, v___x_1447_);
                crate::leanh::lean_ctor_set(v___x_1452_, 1, v___x_1451_);
                v___x_1453_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprLeanOption_repr___redArg___closed__15_once
                    ),
                    _init_l_Lean_instReprLeanOption_repr___redArg___closed__15,
                );
                v___x_1454_ = l_Lean_instReprLeanOption_repr___redArg___closed__16;
                v___x_1455_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1454_);
                crate::leanh::lean_ctor_set(v___x_1455_, 1, v___x_1452_);
                v___x_1456_ = l_Lean_instReprLeanOption_repr___redArg___closed__17;
                v___x_1457_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1455_);
                crate::leanh::lean_ctor_set(v___x_1457_, 1, v___x_1456_);
                v___x_1458_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1453_);
                crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                v___x_1459_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1459_, 0, v___x_1458_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1459_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1438_,
                );
                return v___x_1459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprLeanOption_repr(
    mut v_x_1462_: *mut crate::leanh::LeanObject,
    mut v_prec_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = l_Lean_instReprLeanOption_repr___redArg(v_x_1462_);
    return v___x_1464_;
}
pub unsafe fn l_Lean_instReprLeanOption_repr___boxed(
    mut v_x_1465_: *mut crate::leanh::LeanObject,
    mut v_prec_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Lean_instReprLeanOption_repr(v_x_1465_, v_prec_1466_);
    crate::leanh::lean_dec(v_prec_1466_);
    return v_res_1467_;
}
pub unsafe fn l_Lean_LeanOption_asCliArg(
    mut v_o_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1473_ = crate::leanh::lean_ctor_get(v_o_1472_, 0);
    crate::leanh::lean_inc(v_name_1473_);
    v_value_1474_ = crate::leanh::lean_ctor_get(v_o_1472_, 1);
    crate::leanh::lean_inc_ref(v_value_1474_);
    crate::leanh::lean_dec_ref(v_o_1472_);
    v___x_1475_ = l_Lean_LeanOption_asCliArg___closed__0;
    v___x_1476_ = 1;
    v___x_1477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1473_,
        v___x_1476_,
    );
    v___x_1478_ = lean_string_append(v___x_1475_, v___x_1477_);
    crate::leanh::lean_dec_ref(v___x_1477_);
    v___x_1479_ = l_Lean_LeanOption_asCliArg___closed__1;
    v___x_1480_ = lean_string_append(v___x_1478_, v___x_1479_);
    v___x_1481_ = l_Lean_LeanOptionValue_asCliFlagValue(v_value_1474_);
    v___x_1482_ = lean_string_append(v___x_1480_, v___x_1481_);
    crate::leanh::lean_dec_ref(v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lean_instInhabitedLeanOptions_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = crate::leanh::lean_box(1);
    return v___x_1483_;
}
pub unsafe fn _init_l_Lean_instInhabitedLeanOptions() -> *mut crate::leanh::LeanObject {
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = crate::leanh::lean_box(1);
    return v___x_1484_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(
    mut v_x_1485_: *mut crate::leanh::LeanObject,
    mut v_x_1486_: *mut crate::leanh::LeanObject,
    mut v_x_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1487_) == 0 {
                    crate::leanh::lean_dec(v_x_1485_);
                    return v_x_1486_;
                } else {
                    v_head_1488_ = crate::leanh::lean_ctor_get(v_x_1487_, 0);
                    v_tail_1489_ = crate::leanh::lean_ctor_get(v_x_1487_, 1);
                    v_isSharedCheck_1498_ = (!crate::leanh::lean_is_exclusive(v_x_1487_)) as u8;
                    if v_isSharedCheck_1498_ == 0 {
                        v___x_1491_ = v_x_1487_;
                        v_isShared_1492_ = v_isSharedCheck_1498_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1489_);
                        crate::leanh::lean_inc(v_head_1488_);
                        crate::leanh::lean_dec(v_x_1487_);
                        v___x_1491_ = crate::leanh::lean_box(0);
                        v_isShared_1492_ = v_isSharedCheck_1498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1485_);
                if v_isShared_1492_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1491_, 5);
                    crate::leanh::lean_ctor_set(v___x_1491_, 1, v_x_1485_);
                    crate::leanh::lean_ctor_set(v___x_1491_, 0, v_x_1486_);
                    v___x_1494_ = v___x_1491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_x_1486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_x_1485_);
                    v___x_1494_ = v_reuseFailAlloc_1497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1495_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                crate::leanh::lean_ctor_set(v___x_1495_, 1, v_head_1488_);
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
    mut v_x_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1499_) == 0 {
        let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1500_);
        v___x_1501_ = crate::leanh::lean_box(0);
        return v___x_1501_;
    } else {
        let mut v_tail_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1502_ = crate::leanh::lean_ctor_get(v_x_1499_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1502_) == 0 {
            let mut v_head_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1500_);
            v_head_1503_ = crate::leanh::lean_ctor_get(v_x_1499_, 0);
            crate::leanh::lean_inc(v_head_1503_);
            crate::leanh::lean_dec_ref_known(v_x_1499_, 2);
            return v_head_1503_;
        } else {
            let mut v_head_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1502_);
            v_head_1504_ = crate::leanh::lean_ctor_get(v_x_1499_, 0);
            crate::leanh::lean_inc(v_head_1504_);
            crate::leanh::lean_dec_ref_known(v_x_1499_, 2);
            v___x_1505_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2_spec__3(v_x_1500_, v_head_1504_, v_tail_1502_);
            return v___x_1505_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__0;
    v___x_1512_ = lean_string_length(v___x_1511_);
    return v___x_1512_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__3);
    v___x_1514_ = lean_nat_to_int(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(
    mut v_x_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1520_ = crate::leanh::lean_ctor_get(v_x_1519_, 0);
                v_snd_1521_ = crate::leanh::lean_ctor_get(v_x_1519_, 1);
                v_isSharedCheck_1544_ = (!crate::leanh::lean_is_exclusive(v_x_1519_)) as u8;
                if v_isSharedCheck_1544_ == 0 {
                    v___x_1523_ = v_x_1519_;
                    v_isShared_1524_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1521_);
                    crate::leanh::lean_inc(v_fst_1520_);
                    crate::leanh::lean_dec(v_x_1519_);
                    v___x_1523_ = crate::leanh::lean_box(0);
                    v_isShared_1524_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1525_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1526_ = l_Lean_Name_reprPrec(v_fst_1520_, v___x_1525_);
                v___x_1527_ = crate::leanh::lean_box(0);
                if v_isShared_1524_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1523_, 1);
                    crate::leanh::lean_ctor_set(v___x_1523_, 1, v___x_1527_);
                    crate::leanh::lean_ctor_set(v___x_1523_, 0, v___x_1526_);
                    v___x_1529_ = v___x_1523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1530_ = l_Lean_instReprLeanOptionValue_repr(v_snd_1521_, v___x_1525_);
                v___x_1531_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
                crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1529_);
                v___x_1532_ = l_List_reverse___redArg(v___x_1531_);
                v___x_1533_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1;
                v___x_1534_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1_spec__2(v___x_1532_, v___x_1533_);
                v___x_1535_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__4);
                v___x_1536_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__5;
                v___x_1537_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                crate::leanh::lean_ctor_set(v___x_1537_, 1, v___x_1534_);
                v___x_1538_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__6;
                v___x_1539_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1539_, 0, v___x_1537_);
                crate::leanh::lean_ctor_set(v___x_1539_, 1, v___x_1538_);
                v___x_1540_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1535_);
                crate::leanh::lean_ctor_set(v___x_1540_, 1, v___x_1539_);
                v___x_1541_ = 0;
                v___x_1542_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1540_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1541_,
                );
                return v___x_1542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(
    mut v_x_1545_: *mut crate::leanh::LeanObject,
    mut v_x_1546_: *mut crate::leanh::LeanObject,
    mut v_x_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1552_: u8 = 0;
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1547_) == 0 {
                    crate::leanh::lean_dec(v_x_1545_);
                    return v_x_1546_;
                } else {
                    v_head_1548_ = crate::leanh::lean_ctor_get(v_x_1547_, 0);
                    v_tail_1549_ = crate::leanh::lean_ctor_get(v_x_1547_, 1);
                    v_isSharedCheck_1559_ = (!crate::leanh::lean_is_exclusive(v_x_1547_)) as u8;
                    if v_isSharedCheck_1559_ == 0 {
                        v___x_1551_ = v_x_1547_;
                        v_isShared_1552_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1549_);
                        crate::leanh::lean_inc(v_head_1548_);
                        crate::leanh::lean_dec(v_x_1547_);
                        v___x_1551_ = crate::leanh::lean_box(0);
                        v_isShared_1552_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1545_);
                if v_isShared_1552_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1551_, 5);
                    crate::leanh::lean_ctor_set(v___x_1551_, 1, v_x_1545_);
                    crate::leanh::lean_ctor_set(v___x_1551_, 0, v_x_1546_);
                    v___x_1554_ = v___x_1551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_x_1546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_x_1545_);
                    v___x_1554_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1555_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1548_);
                v___x_1556_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1556_, 0, v___x_1554_);
                crate::leanh::lean_ctor_set(v___x_1556_, 1, v___x_1555_);
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
    mut v_x_1560_: *mut crate::leanh::LeanObject,
    mut v_x_1561_: *mut crate::leanh::LeanObject,
    mut v_x_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1562_) == 0 {
                    crate::leanh::lean_dec(v_x_1560_);
                    return v_x_1561_;
                } else {
                    v_head_1563_ = crate::leanh::lean_ctor_get(v_x_1562_, 0);
                    v_tail_1564_ = crate::leanh::lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1574_ = (!crate::leanh::lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1574_ == 0 {
                        v___x_1566_ = v_x_1562_;
                        v_isShared_1567_ = v_isSharedCheck_1574_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1564_);
                        crate::leanh::lean_inc(v_head_1563_);
                        crate::leanh::lean_dec(v_x_1562_);
                        v___x_1566_ = crate::leanh::lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1574_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_1560_);
                if v_isShared_1567_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1566_, 5);
                    crate::leanh::lean_ctor_set(v___x_1566_, 1, v_x_1560_);
                    crate::leanh::lean_ctor_set(v___x_1566_, 0, v_x_1561_);
                    v___x_1569_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1573_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_x_1561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_x_1560_);
                    v___x_1569_ = v_reuseFailAlloc_1573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1570_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1563_);
                v___x_1571_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1571_, 0, v___x_1569_);
                crate::leanh::lean_ctor_set(v___x_1571_, 1, v___x_1570_);
                v___x_1572_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4_spec__6(v_x_1560_, v___x_1571_, v_tail_1564_);
                return v___x_1572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(
    mut v_x_1575_: *mut crate::leanh::LeanObject,
    mut v_x_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1575_) == 0 {
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_1576_);
        v___x_1577_ = crate::leanh::lean_box(0);
        return v___x_1577_;
    } else {
        let mut v_tail_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_1578_ = crate::leanh::lean_ctor_get(v_x_1575_, 1);
        if crate::leanh::lean_obj_tag(v_tail_1578_) == 0 {
            let mut v_head_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_1576_);
            v_head_1579_ = crate::leanh::lean_ctor_get(v_x_1575_, 0);
            crate::leanh::lean_inc(v_head_1579_);
            crate::leanh::lean_dec_ref_known(v_x_1575_, 2);
            v___x_1580_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1579_);
            return v___x_1580_;
        } else {
            let mut v_head_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_1578_);
            v_head_1581_ = crate::leanh::lean_ctor_get(v_x_1575_, 0);
            crate::leanh::lean_inc(v_head_1581_);
            crate::leanh::lean_dec_ref_known(v_x_1575_, 2);
            v___x_1582_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_head_1581_);
            v___x_1583_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2_spec__4(v_x_1576_, v___x_1582_, v_tail_1578_);
            return v___x_1583_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__2;
    v___x_1590_ = lean_string_length(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = crate::leanh::lean_obj_once(
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
    mut v_a_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_1597_) == 0 {
        let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1598_ =
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__1;
        return v___x_1598_;
    } else {
        let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: u8 = 0;
        let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1599_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg___closed__1;
        v___x_1600_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__2(v_a_1597_, v___x_1599_);
        v___x_1601_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5_once), _init_l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__5);
        v___x_1602_ =
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__6;
        v___x_1603_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1603_, 0, v___x_1602_);
        crate::leanh::lean_ctor_set(v___x_1603_, 1, v___x_1600_);
        v___x_1604_ =
            l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg___closed__7;
        v___x_1605_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1605_, 0, v___x_1603_);
        crate::leanh::lean_ctor_set(v___x_1605_, 1, v___x_1604_);
        v___x_1606_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1601_);
        crate::leanh::lean_ctor_set(v___x_1606_, 1, v___x_1605_);
        v___x_1607_ = 0;
        v___x_1608_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_1608_, 0, v___x_1606_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_1608_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_1607_,
        );
        return v___x_1608_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(
    mut v_init_1609_: *mut crate::leanh::LeanObject,
    mut v_x_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1610_) == 0 {
                    v_k_1611_ = crate::leanh::lean_ctor_get(v_x_1610_, 1);
                    v_v_1612_ = crate::leanh::lean_ctor_get(v_x_1610_, 2);
                    v_l_1613_ = crate::leanh::lean_ctor_get(v_x_1610_, 3);
                    v_r_1614_ = crate::leanh::lean_ctor_get(v_x_1610_, 4);
                    v___x_1615_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(v_init_1609_, v_r_1614_);
                    crate::leanh::lean_inc(v_v_1612_);
                    crate::leanh::lean_inc(v_k_1611_);
                    v___x_1616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1616_, 0, v_k_1611_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 1, v_v_1612_);
                    v___x_1617_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
                    crate::leanh::lean_ctor_set(v___x_1617_, 1, v___x_1615_);
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
    mut v_init_1619_: *mut crate::leanh::LeanObject,
    mut v_x_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1621_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(
            v_init_1619_,
            v_x_1620_,
        );
    crate::leanh::lean_dec(v_x_1620_);
    return v_res_1621_;
}
pub unsafe fn _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1632_ = lean_nat_to_int(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr___redArg(
    mut v_x_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Lean_instReprLeanOptions_repr___redArg___closed__3;
    v___x_1638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptions_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOptions_repr___redArg___closed__4_once),
        _init_l_Lean_instReprLeanOptions_repr___redArg___closed__4,
    );
    v___x_1639_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1640_ = l_Lean_instReprLeanOptions_repr___redArg___closed__6;
    v___x_1641_ = crate::leanh::lean_box(0);
    v___x_1642_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprLeanOptions_repr_spec__0(
            v___x_1641_,
            v_x_1636_,
        );
    v___x_1643_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v___x_1642_);
    v___x_1644_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1644_, 0, v___x_1640_);
    crate::leanh::lean_ctor_set(v___x_1644_, 1, v___x_1643_);
    v___x_1645_ = l_Repr_addAppParen(v___x_1644_, v___x_1639_);
    v___x_1646_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1638_);
    crate::leanh::lean_ctor_set(v___x_1646_, 1, v___x_1645_);
    v___x_1647_ = 0;
    v___x_1648_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1646_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1648_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1647_,
    );
    v___x_1649_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1649_, 0, v___x_1637_);
    crate::leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
    v___x_1650_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprLeanOption_repr___redArg___closed__15_once),
        _init_l_Lean_instReprLeanOption_repr___redArg___closed__15,
    );
    v___x_1651_ = l_Lean_instReprLeanOption_repr___redArg___closed__16;
    v___x_1652_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1651_);
    crate::leanh::lean_ctor_set(v___x_1652_, 1, v___x_1649_);
    v___x_1653_ = l_Lean_instReprLeanOption_repr___redArg___closed__17;
    v___x_1654_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1654_, 0, v___x_1652_);
    crate::leanh::lean_ctor_set(v___x_1654_, 1, v___x_1653_);
    v___x_1655_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1655_, 0, v___x_1650_);
    crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
    v___x_1656_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1655_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1656_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1647_,
    );
    return v___x_1656_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr___redArg___boxed(
    mut v_x_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_1657_);
    crate::leanh::lean_dec(v_x_1657_);
    return v_res_1658_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr(
    mut v_x_1659_: *mut crate::leanh::LeanObject,
    mut v_prec_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Lean_instReprLeanOptions_repr___redArg(v_x_1659_);
    return v___x_1661_;
}
pub unsafe fn l_Lean_instReprLeanOptions_repr___boxed(
    mut v_x_1662_: *mut crate::leanh::LeanObject,
    mut v_prec_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_instReprLeanOptions_repr(v_x_1662_, v_prec_1663_);
    crate::leanh::lean_dec(v_prec_1663_);
    crate::leanh::lean_dec(v_x_1662_);
    return v_res_1664_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(
    mut v_a_1665_: *mut crate::leanh::LeanObject,
    mut v_n_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___redArg(v_a_1665_);
    return v___x_1667_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1___boxed(
    mut v_a_1668_: *mut crate::leanh::LeanObject,
    mut v_n_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_List_repr___at___00Lean_instReprLeanOptions_repr_spec__1(v_a_1668_, v_n_1669_);
    crate::leanh::lean_dec(v_n_1669_);
    return v_res_1670_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(
    mut v_x_1671_: *mut crate::leanh::LeanObject,
    mut v_x_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___redArg(v_x_1671_);
    return v___x_1673_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1___boxed(
    mut v_x_1674_: *mut crate::leanh::LeanObject,
    mut v_x_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1676_ =
        l_Prod_repr___at___00List_repr___at___00Lean_instReprLeanOptions_repr_spec__1_spec__1(
            v_x_1674_, v_x_1675_,
        );
    crate::leanh::lean_dec(v_x_1675_);
    return v_res_1676_;
}
pub unsafe fn _init_l_Lean_instEmptyCollectionLeanOptions() -> *mut crate::leanh::LeanObject {
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1679_ = crate::leanh::lean_box(1);
    return v___x_1679_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(
    mut v_as_1680_: *mut crate::leanh::LeanObject,
    mut v_i_1681_: usize,
    mut v_stop_1682_: usize,
    mut v_b_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: usize = 0;
    let mut v___x_1690_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1684_ = lean_usize_dec_eq(v_i_1681_, v_stop_1682_);
                if v___x_1684_ == 0 {
                    v___x_1685_ = lean_array_uget_borrowed(v_as_1680_, v_i_1681_);
                    v_name_1686_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                    v_value_1687_ = crate::leanh::lean_ctor_get(v___x_1685_, 1);
                    crate::leanh::lean_inc_ref(v_value_1687_);
                    crate::leanh::lean_inc(v_name_1686_);
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
    mut v_as_1692_: *mut crate::leanh::LeanObject,
    mut v_i_1693_: *mut crate::leanh::LeanObject,
    mut v_stop_1694_: *mut crate::leanh::LeanObject,
    mut v_b_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1696_: usize = 0;
    let mut v_stop_boxed_1697_: usize = 0;
    let mut v_res_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1696_ = crate::leanh::lean_unbox_usize(v_i_1693_);
    crate::leanh::lean_dec(v_i_1693_);
    v_stop_boxed_1697_ = crate::leanh::lean_unbox_usize(v_stop_1694_);
    crate::leanh::lean_dec(v_stop_1694_);
    v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_as_1692_, v_i_boxed_1696_, v_stop_boxed_1697_, v_b_1695_);
    crate::leanh::lean_dec_ref(v_as_1692_);
    return v_res_1698_;
}
pub unsafe fn l_Lean_LeanOptions_ofArray(
    mut v_opts_1699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: u8 = 0;
    v___x_1700_ = crate::leanh::lean_box(1);
    v___x_1701_ = crate::leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1705_ = 0usize;
                v___x_1706_ = lean_usize_of_nat(v___x_1702_);
                v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_1699_, v___x_1705_, v___x_1706_, v___x_1700_);
                return v___x_1707_;
            }
        } else {
            let mut v___x_1708_: usize = 0;
            let mut v___x_1709_: usize = 0;
            let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1708_ = 0usize;
            v___x_1709_ = lean_usize_of_nat(v___x_1702_);
            v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_opts_1699_, v___x_1708_, v___x_1709_, v___x_1700_);
            return v___x_1710_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_ofArray___boxed(
    mut v_opts_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lean_LeanOptions_ofArray(v_opts_1711_);
    crate::leanh::lean_dec_ref(v_opts_1711_);
    return v_res_1712_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(
    mut v_b_u2082_1713_: *mut crate::leanh::LeanObject,
    mut v_k_1714_: *mut crate::leanh::LeanObject,
    mut v_t_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: u8 = 0;
    let mut v_impl_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1715_) == 0 {
                    v_size_1716_ = crate::leanh::lean_ctor_get(v_t_1715_, 0);
                    v_k_1717_ = crate::leanh::lean_ctor_get(v_t_1715_, 1);
                    v_v_1718_ = crate::leanh::lean_ctor_get(v_t_1715_, 2);
                    v_l_1719_ = crate::leanh::lean_ctor_get(v_t_1715_, 3);
                    v_r_1720_ = crate::leanh::lean_ctor_get(v_t_1715_, 4);
                    v_isSharedCheck_1732_ = (!crate::leanh::lean_is_exclusive(v_t_1715_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1722_ = v_t_1715_;
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1720_);
                        crate::leanh::lean_inc(v_l_1719_);
                        crate::leanh::lean_inc(v_v_1718_);
                        crate::leanh::lean_inc(v_k_1717_);
                        crate::leanh::lean_inc(v_size_1716_);
                        crate::leanh::lean_dec(v_t_1715_);
                        v___x_1722_ = crate::leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1733_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1734_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1734_, 0, v___x_1733_);
                    crate::leanh::lean_ctor_set(v___x_1734_, 1, v_k_1714_);
                    crate::leanh::lean_ctor_set(v___x_1734_, 2, v_b_u2082_1713_);
                    crate::leanh::lean_ctor_set(v___x_1734_, 3, v_t_1715_);
                    crate::leanh::lean_ctor_set(v___x_1734_, 4, v_t_1715_);
                    return v___x_1734_;
                }
            }
            1 => {
                v___x_1724_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1714_, v_k_1717_);
                match v___x_1724_ {
                    0 => {
                        crate::leanh::lean_del_object(v___x_1722_);
                        crate::leanh::lean_dec(v_size_1716_);
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
                        crate::leanh::lean_dec(v_v_1718_);
                        crate::leanh::lean_dec(v_k_1717_);
                        if v_isShared_1723_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1722_, 2, v_b_u2082_1713_);
                            crate::leanh::lean_ctor_set(v___x_1722_, 1, v_k_1714_);
                            v___x_1728_ = v___x_1722_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1729_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_size_1716_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_k_1714_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_b_u2082_1713_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_l_1719_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_r_1720_);
                            v___x_1728_ = v_reuseFailAlloc_1729_;
                            state = 2;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_del_object(v___x_1722_);
                        crate::leanh::lean_dec(v_size_1716_);
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
    mut v_init_1735_: *mut crate::leanh::LeanObject,
    mut v_x_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1736_) == 0 {
                    v_k_1737_ = crate::leanh::lean_ctor_get(v_x_1736_, 1);
                    crate::leanh::lean_inc(v_k_1737_);
                    v_v_1738_ = crate::leanh::lean_ctor_get(v_x_1736_, 2);
                    crate::leanh::lean_inc(v_v_1738_);
                    v_l_1739_ = crate::leanh::lean_ctor_get(v_x_1736_, 3);
                    crate::leanh::lean_inc(v_l_1739_);
                    v_r_1740_ = crate::leanh::lean_ctor_get(v_x_1736_, 4);
                    crate::leanh::lean_inc(v_r_1740_);
                    crate::leanh::lean_dec_ref_known(v_x_1736_, 5);
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
    mut v_self_1744_: *mut crate::leanh::LeanObject,
    mut v_new_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_self_1744_, v_new_1745_);
    return v___x_1746_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0(
    mut v_b_u2082_1747_: *mut crate::leanh::LeanObject,
    mut v_k_1748_: *mut crate::leanh::LeanObject,
    mut v_t_1749_: *mut crate::leanh::LeanObject,
    mut v_hl_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ =
        l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LeanOptions_append_spec__0___redArg(
            v_b_u2082_1747_,
            v_k_1748_,
            v_t_1749_,
        );
    return v___x_1751_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1(
    mut v_init_1752_: *mut crate::leanh::LeanObject,
    mut v_t_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LeanOptions_append_spec__1_spec__1(v_init_1752_, v_t_1753_);
    return v___x_1754_;
}
pub unsafe fn l_Lean_LeanOptions_appendArray(
    mut v_self_1757_: *mut crate::leanh::LeanObject,
    mut v_new_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    v___x_1759_ = crate::leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1763_ = 0usize;
                v___x_1764_ = lean_usize_of_nat(v___x_1760_);
                v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_1758_, v___x_1763_, v___x_1764_, v_self_1757_);
                return v___x_1765_;
            }
        } else {
            let mut v___x_1766_: usize = 0;
            let mut v___x_1767_: usize = 0;
            let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1766_ = 0usize;
            v___x_1767_ = lean_usize_of_nat(v___x_1760_);
            v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LeanOptions_ofArray_spec__0(v_new_1758_, v___x_1766_, v___x_1767_, v_self_1757_);
            return v___x_1768_;
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_appendArray___boxed(
    mut v_self_1769_: *mut crate::leanh::LeanObject,
    mut v_new_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Lean_LeanOptions_appendArray(v_self_1769_, v_new_1770_);
    crate::leanh::lean_dec_ref(v_new_1770_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0(
    mut v_o_1777_: *mut crate::leanh::LeanObject,
    mut v_k_1778_: *mut crate::leanh::LeanObject,
    mut v_v_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1781_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1780_ = crate::leanh::lean_ctor_get(v_o_1777_, 0);
                v_hasTrace_1781_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_1777_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1794_ = (!crate::leanh::lean_is_exclusive(v_o_1777_)) as u8;
                if v_isSharedCheck_1794_ == 0 {
                    v___x_1783_ = v_o_1777_;
                    v_isShared_1784_ = v_isSharedCheck_1794_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_1780_);
                    crate::leanh::lean_dec(v_o_1777_);
                    v___x_1783_ = crate::leanh::lean_box(0);
                    v_isShared_1784_ = v_isSharedCheck_1794_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_k_1778_);
                v___x_1785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1778_, v_v_1779_, v_map_1780_);
                if v_hasTrace_1781_ == 0 {
                    v___x_1786_ =
                        l_Lean_Options_set___at___00Lean_LeanOptions_toOptions_spec__0___closed__1;
                    v___x_1787_ = l_Lean_Name_isPrefixOf(v___x_1786_, v_k_1778_);
                    crate::leanh::lean_dec(v_k_1778_);
                    if v_isShared_1784_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1785_);
                        v___x_1789_ = v___x_1783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1785_);
                        v___x_1789_ = v_reuseFailAlloc_1790_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1778_);
                    if v_isShared_1784_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1785_);
                        v___x_1792_ = v___x_1783_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1785_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1793_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1781_,
                        );
                        v___x_1792_ = v_reuseFailAlloc_1793_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1789_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_init_1795_: *mut crate::leanh::LeanObject,
    mut v_x_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1796_) == 0 {
                    v_k_1797_ = crate::leanh::lean_ctor_get(v_x_1796_, 1);
                    crate::leanh::lean_inc(v_k_1797_);
                    v_v_1798_ = crate::leanh::lean_ctor_get(v_x_1796_, 2);
                    crate::leanh::lean_inc(v_v_1798_);
                    v_l_1799_ = crate::leanh::lean_ctor_get(v_x_1796_, 3);
                    crate::leanh::lean_inc(v_l_1799_);
                    v_r_1800_ = crate::leanh::lean_ctor_get(v_x_1796_, 4);
                    crate::leanh::lean_inc(v_r_1800_);
                    crate::leanh::lean_dec_ref_known(v_x_1796_, 5);
                    v___x_1801_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(v_init_1795_, v_l_1799_);
                    v_a_1802_ = crate::leanh::lean_ctor_get(v___x_1801_, 0);
                    crate::leanh::lean_inc(v_a_1802_);
                    crate::leanh::lean_dec_ref(v___x_1801_);
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
                    v___x_1806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1806_, 0, v_init_1795_);
                    return v___x_1806_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_toOptions(
    mut v_leanOptions_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_1808_ = l_Lean_Options_empty;
    v___x_1809_ =
        l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_toOptions_spec__1(
            v_options_1808_,
            v_leanOptions_1807_,
        );
    v_a_1810_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
    crate::leanh::lean_inc(v_a_1810_);
    crate::leanh::lean_dec_ref(v___x_1809_);
    return v_a_1810_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(
    mut v_k_1811_: *mut crate::leanh::LeanObject,
    mut v_v_1812_: *mut crate::leanh::LeanObject,
    mut v_t_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v_impl_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v_size_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v_unused_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_unused_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1924_: u8 = 0;
    let mut v_unused_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v_k_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v_unused_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v_size_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2018_: u8 = 0;
    let mut v_unused_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2031_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_unused_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut v_unused_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v_k_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_unused_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_unused_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1813_) == 0 {
                    v_size_1814_ = crate::leanh::lean_ctor_get(v_t_1813_, 0);
                    v_k_1815_ = crate::leanh::lean_ctor_get(v_t_1813_, 1);
                    v_v_1816_ = crate::leanh::lean_ctor_get(v_t_1813_, 2);
                    v_l_1817_ = crate::leanh::lean_ctor_get(v_t_1813_, 3);
                    v_r_1818_ = crate::leanh::lean_ctor_get(v_t_1813_, 4);
                    v_isSharedCheck_2098_ = (!crate::leanh::lean_is_exclusive(v_t_1813_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_1820_ = v_t_1813_;
                        v_isShared_1821_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1818_);
                        crate::leanh::lean_inc(v_l_1817_);
                        crate::leanh::lean_inc(v_v_1816_);
                        crate::leanh::lean_inc(v_k_1815_);
                        crate::leanh::lean_inc(v_size_1814_);
                        crate::leanh::lean_dec(v_t_1813_);
                        v___x_1820_ = crate::leanh::lean_box(0);
                        v_isShared_1821_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2099_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2100_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2100_, 0, v___x_2099_);
                    crate::leanh::lean_ctor_set(v___x_2100_, 1, v_k_1811_);
                    crate::leanh::lean_ctor_set(v___x_2100_, 2, v_v_1812_);
                    crate::leanh::lean_ctor_set(v___x_2100_, 3, v_t_1813_);
                    crate::leanh::lean_ctor_set(v___x_2100_, 4, v_t_1813_);
                    return v___x_2100_;
                }
            }
            1 => {
                v___x_1822_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1811_, v_k_1815_);
                match v___x_1822_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1814_);
                        v_impl_1823_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1811_, v_v_1812_, v_l_1817_);
                        v___x_1824_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_1818_) == 0 {
                            v_size_1825_ = crate::leanh::lean_ctor_get(v_r_1818_, 0);
                            v_size_1826_ = crate::leanh::lean_ctor_get(v_impl_1823_, 0);
                            crate::leanh::lean_inc(v_size_1826_);
                            v_k_1827_ = crate::leanh::lean_ctor_get(v_impl_1823_, 1);
                            crate::leanh::lean_inc(v_k_1827_);
                            v_v_1828_ = crate::leanh::lean_ctor_get(v_impl_1823_, 2);
                            crate::leanh::lean_inc(v_v_1828_);
                            v_l_1829_ = crate::leanh::lean_ctor_get(v_impl_1823_, 3);
                            crate::leanh::lean_inc(v_l_1829_);
                            v_r_1830_ = crate::leanh::lean_ctor_get(v_impl_1823_, 4);
                            crate::leanh::lean_inc(v_r_1830_);
                            v___x_1831_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1832_ = lean_nat_mul(v___x_1831_, v_size_1825_);
                            v___x_1833_ = lean_nat_dec_lt(v___x_1832_, v_size_1826_);
                            crate::leanh::lean_dec(v___x_1832_);
                            if v___x_1833_ == 0 {
                                crate::leanh::lean_dec(v_r_1830_);
                                crate::leanh::lean_dec(v_l_1829_);
                                crate::leanh::lean_dec(v_v_1828_);
                                crate::leanh::lean_dec(v_k_1827_);
                                v___x_1834_ = lean_nat_add(v___x_1824_, v_size_1826_);
                                crate::leanh::lean_dec(v_size_1826_);
                                v___x_1835_ = lean_nat_add(v___x_1834_, v_size_1825_);
                                crate::leanh::lean_dec(v___x_1834_);
                                if v_isShared_1821_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1820_, 3, v_impl_1823_);
                                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1835_);
                                    v___x_1837_ = v___x_1820_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1838_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        0,
                                        v___x_1835_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        1,
                                        v_k_1815_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        2,
                                        v_v_1816_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1838_,
                                        3,
                                        v_impl_1823_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_1823_)) as u8;
                                if v_isSharedCheck_1904_ == 0 {
                                    v_unused_1905_ = crate::leanh::lean_ctor_get(v_impl_1823_, 4);
                                    crate::leanh::lean_dec(v_unused_1905_);
                                    v_unused_1906_ = crate::leanh::lean_ctor_get(v_impl_1823_, 3);
                                    crate::leanh::lean_dec(v_unused_1906_);
                                    v_unused_1907_ = crate::leanh::lean_ctor_get(v_impl_1823_, 2);
                                    crate::leanh::lean_dec(v_unused_1907_);
                                    v_unused_1908_ = crate::leanh::lean_ctor_get(v_impl_1823_, 1);
                                    crate::leanh::lean_dec(v_unused_1908_);
                                    v_unused_1909_ = crate::leanh::lean_ctor_get(v_impl_1823_, 0);
                                    crate::leanh::lean_dec(v_unused_1909_);
                                    v___x_1840_ = v_impl_1823_;
                                    v_isShared_1841_ = v_isSharedCheck_1904_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1823_);
                                    v___x_1840_ = crate::leanh::lean_box(0);
                                    v_isShared_1841_ = v_isSharedCheck_1904_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1910_ = crate::leanh::lean_ctor_get(v_impl_1823_, 3);
                            crate::leanh::lean_inc(v_l_1910_);
                            if crate::leanh::lean_obj_tag(v_l_1910_) == 0 {
                                v_r_1911_ = crate::leanh::lean_ctor_get(v_impl_1823_, 4);
                                v_k_1912_ = crate::leanh::lean_ctor_get(v_impl_1823_, 1);
                                v_v_1913_ = crate::leanh::lean_ctor_get(v_impl_1823_, 2);
                                v_isSharedCheck_1924_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1823_)) as u8;
                                if v_isSharedCheck_1924_ == 0 {
                                    v_unused_1925_ = crate::leanh::lean_ctor_get(v_impl_1823_, 3);
                                    crate::leanh::lean_dec(v_unused_1925_);
                                    v_unused_1926_ = crate::leanh::lean_ctor_get(v_impl_1823_, 0);
                                    crate::leanh::lean_dec(v_unused_1926_);
                                    v___x_1915_ = v_impl_1823_;
                                    v_isShared_1916_ = v_isSharedCheck_1924_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1911_);
                                    crate::leanh::lean_inc(v_v_1913_);
                                    crate::leanh::lean_inc(v_k_1912_);
                                    crate::leanh::lean_dec(v_impl_1823_);
                                    v___x_1915_ = crate::leanh::lean_box(0);
                                    v_isShared_1916_ = v_isSharedCheck_1924_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1927_ = crate::leanh::lean_ctor_get(v_impl_1823_, 4);
                                crate::leanh::lean_inc(v_r_1927_);
                                if crate::leanh::lean_obj_tag(v_r_1927_) == 0 {
                                    v_k_1928_ = crate::leanh::lean_ctor_get(v_impl_1823_, 1);
                                    v_v_1929_ = crate::leanh::lean_ctor_get(v_impl_1823_, 2);
                                    v_isSharedCheck_1952_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1823_)) as u8;
                                    if v_isSharedCheck_1952_ == 0 {
                                        v_unused_1953_ =
                                            crate::leanh::lean_ctor_get(v_impl_1823_, 4);
                                        crate::leanh::lean_dec(v_unused_1953_);
                                        v_unused_1954_ =
                                            crate::leanh::lean_ctor_get(v_impl_1823_, 3);
                                        crate::leanh::lean_dec(v_unused_1954_);
                                        v_unused_1955_ =
                                            crate::leanh::lean_ctor_get(v_impl_1823_, 0);
                                        crate::leanh::lean_dec(v_unused_1955_);
                                        v___x_1931_ = v_impl_1823_;
                                        v_isShared_1932_ = v_isSharedCheck_1952_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1929_);
                                        crate::leanh::lean_inc(v_k_1928_);
                                        crate::leanh::lean_dec(v_impl_1823_);
                                        v___x_1931_ = crate::leanh::lean_box(0);
                                        v_isShared_1932_ = v_isSharedCheck_1952_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1956_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1821_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1820_, 4, v_r_1927_);
                                        crate::leanh::lean_ctor_set(v___x_1820_, 3, v_impl_1823_);
                                        crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1956_);
                                        v___x_1958_ = v___x_1820_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1959_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            0,
                                            v___x_1956_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            1,
                                            v_k_1815_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            2,
                                            v_v_1816_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1959_,
                                            3,
                                            v_impl_1823_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_v_1816_);
                        crate::leanh::lean_dec(v_k_1815_);
                        if v_isShared_1821_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1820_, 2, v_v_1812_);
                            crate::leanh::lean_ctor_set(v___x_1820_, 1, v_k_1811_);
                            v___x_1961_ = v___x_1820_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1962_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_size_1814_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_k_1811_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_v_1812_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_l_1817_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_r_1818_);
                            v___x_1961_ = v_reuseFailAlloc_1962_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1814_);
                        v_impl_1963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_1811_, v_v_1812_, v_r_1818_);
                        v___x_1964_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1817_) == 0 {
                            v_size_1965_ = crate::leanh::lean_ctor_get(v_l_1817_, 0);
                            v_size_1966_ = crate::leanh::lean_ctor_get(v_impl_1963_, 0);
                            crate::leanh::lean_inc(v_size_1966_);
                            v_k_1967_ = crate::leanh::lean_ctor_get(v_impl_1963_, 1);
                            crate::leanh::lean_inc(v_k_1967_);
                            v_v_1968_ = crate::leanh::lean_ctor_get(v_impl_1963_, 2);
                            crate::leanh::lean_inc(v_v_1968_);
                            v_l_1969_ = crate::leanh::lean_ctor_get(v_impl_1963_, 3);
                            crate::leanh::lean_inc(v_l_1969_);
                            v_r_1970_ = crate::leanh::lean_ctor_get(v_impl_1963_, 4);
                            crate::leanh::lean_inc(v_r_1970_);
                            v___x_1971_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1972_ = lean_nat_mul(v___x_1971_, v_size_1965_);
                            v___x_1973_ = lean_nat_dec_lt(v___x_1972_, v_size_1966_);
                            crate::leanh::lean_dec(v___x_1972_);
                            if v___x_1973_ == 0 {
                                crate::leanh::lean_dec(v_r_1970_);
                                crate::leanh::lean_dec(v_l_1969_);
                                crate::leanh::lean_dec(v_v_1968_);
                                crate::leanh::lean_dec(v_k_1967_);
                                v___x_1974_ = lean_nat_add(v___x_1964_, v_size_1965_);
                                v___x_1975_ = lean_nat_add(v___x_1974_, v_size_1966_);
                                crate::leanh::lean_dec(v_size_1966_);
                                crate::leanh::lean_dec(v___x_1974_);
                                if v_isShared_1821_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v_impl_1963_);
                                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1975_);
                                    v___x_1977_ = v___x_1820_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1978_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        0,
                                        v___x_1975_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        1,
                                        v_k_1815_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        2,
                                        v_v_1816_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1978_,
                                        3,
                                        v_l_1817_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_1963_)) as u8;
                                if v_isSharedCheck_2042_ == 0 {
                                    v_unused_2043_ = crate::leanh::lean_ctor_get(v_impl_1963_, 4);
                                    crate::leanh::lean_dec(v_unused_2043_);
                                    v_unused_2044_ = crate::leanh::lean_ctor_get(v_impl_1963_, 3);
                                    crate::leanh::lean_dec(v_unused_2044_);
                                    v_unused_2045_ = crate::leanh::lean_ctor_get(v_impl_1963_, 2);
                                    crate::leanh::lean_dec(v_unused_2045_);
                                    v_unused_2046_ = crate::leanh::lean_ctor_get(v_impl_1963_, 1);
                                    crate::leanh::lean_dec(v_unused_2046_);
                                    v_unused_2047_ = crate::leanh::lean_ctor_get(v_impl_1963_, 0);
                                    crate::leanh::lean_dec(v_unused_2047_);
                                    v___x_1980_ = v_impl_1963_;
                                    v_isShared_1981_ = v_isSharedCheck_2042_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1963_);
                                    v___x_1980_ = crate::leanh::lean_box(0);
                                    v_isShared_1981_ = v_isSharedCheck_2042_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2048_ = crate::leanh::lean_ctor_get(v_impl_1963_, 3);
                            crate::leanh::lean_inc(v_l_2048_);
                            if crate::leanh::lean_obj_tag(v_l_2048_) == 0 {
                                v_r_2049_ = crate::leanh::lean_ctor_get(v_impl_1963_, 4);
                                v_k_2050_ = crate::leanh::lean_ctor_get(v_impl_1963_, 1);
                                v_v_2051_ = crate::leanh::lean_ctor_get(v_impl_1963_, 2);
                                v_isSharedCheck_2074_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1963_)) as u8;
                                if v_isSharedCheck_2074_ == 0 {
                                    v_unused_2075_ = crate::leanh::lean_ctor_get(v_impl_1963_, 3);
                                    crate::leanh::lean_dec(v_unused_2075_);
                                    v_unused_2076_ = crate::leanh::lean_ctor_get(v_impl_1963_, 0);
                                    crate::leanh::lean_dec(v_unused_2076_);
                                    v___x_2053_ = v_impl_1963_;
                                    v_isShared_2054_ = v_isSharedCheck_2074_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2049_);
                                    crate::leanh::lean_inc(v_v_2051_);
                                    crate::leanh::lean_inc(v_k_2050_);
                                    crate::leanh::lean_dec(v_impl_1963_);
                                    v___x_2053_ = crate::leanh::lean_box(0);
                                    v_isShared_2054_ = v_isSharedCheck_2074_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_2077_ = crate::leanh::lean_ctor_get(v_impl_1963_, 4);
                                crate::leanh::lean_inc(v_r_2077_);
                                if crate::leanh::lean_obj_tag(v_r_2077_) == 0 {
                                    v_k_2078_ = crate::leanh::lean_ctor_get(v_impl_1963_, 1);
                                    v_v_2079_ = crate::leanh::lean_ctor_get(v_impl_1963_, 2);
                                    v_isSharedCheck_2090_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1963_)) as u8;
                                    if v_isSharedCheck_2090_ == 0 {
                                        v_unused_2091_ =
                                            crate::leanh::lean_ctor_get(v_impl_1963_, 4);
                                        crate::leanh::lean_dec(v_unused_2091_);
                                        v_unused_2092_ =
                                            crate::leanh::lean_ctor_get(v_impl_1963_, 3);
                                        crate::leanh::lean_dec(v_unused_2092_);
                                        v_unused_2093_ =
                                            crate::leanh::lean_ctor_get(v_impl_1963_, 0);
                                        crate::leanh::lean_dec(v_unused_2093_);
                                        v___x_2081_ = v_impl_1963_;
                                        v_isShared_2082_ = v_isSharedCheck_2090_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2079_);
                                        crate::leanh::lean_inc(v_k_2078_);
                                        crate::leanh::lean_dec(v_impl_1963_);
                                        v___x_2081_ = crate::leanh::lean_box(0);
                                        v_isShared_2082_ = v_isSharedCheck_2090_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_2094_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1821_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1820_, 4, v_impl_1963_);
                                        crate::leanh::lean_ctor_set(v___x_1820_, 3, v_r_2077_);
                                        crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_2094_);
                                        v___x_2096_ = v___x_1820_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2097_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            0,
                                            v___x_2094_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            1,
                                            v_k_1815_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            2,
                                            v_v_1816_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2097_,
                                            3,
                                            v_r_2077_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                v_size_1842_ = crate::leanh::lean_ctor_get(v_l_1829_, 0);
                v_size_1843_ = crate::leanh::lean_ctor_get(v_r_1830_, 0);
                v_k_1844_ = crate::leanh::lean_ctor_get(v_r_1830_, 1);
                v_v_1845_ = crate::leanh::lean_ctor_get(v_r_1830_, 2);
                v_l_1846_ = crate::leanh::lean_ctor_get(v_r_1830_, 3);
                v_r_1847_ = crate::leanh::lean_ctor_get(v_r_1830_, 4);
                v___x_1848_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1849_ = lean_nat_mul(v___x_1848_, v_size_1842_);
                v___x_1850_ = lean_nat_dec_lt(v_size_1843_, v___x_1849_);
                crate::leanh::lean_dec(v___x_1849_);
                if v___x_1850_ == 0 {
                    crate::leanh::lean_inc(v_r_1847_);
                    crate::leanh::lean_inc(v_l_1846_);
                    crate::leanh::lean_inc(v_v_1845_);
                    crate::leanh::lean_inc(v_k_1844_);
                    v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v_r_1830_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v_unused_1880_ = crate::leanh::lean_ctor_get(v_r_1830_, 4);
                        crate::leanh::lean_dec(v_unused_1880_);
                        v_unused_1881_ = crate::leanh::lean_ctor_get(v_r_1830_, 3);
                        crate::leanh::lean_dec(v_unused_1881_);
                        v_unused_1882_ = crate::leanh::lean_ctor_get(v_r_1830_, 2);
                        crate::leanh::lean_dec(v_unused_1882_);
                        v_unused_1883_ = crate::leanh::lean_ctor_get(v_r_1830_, 1);
                        crate::leanh::lean_dec(v_unused_1883_);
                        v_unused_1884_ = crate::leanh::lean_ctor_get(v_r_1830_, 0);
                        crate::leanh::lean_dec(v_unused_1884_);
                        v___x_1852_ = v_r_1830_;
                        v_isShared_1853_ = v_isSharedCheck_1879_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1830_);
                        v___x_1852_ = crate::leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1879_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1820_);
                    v___x_1885_ = lean_nat_add(v___x_1824_, v_size_1826_);
                    crate::leanh::lean_dec(v_size_1826_);
                    v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1825_);
                    crate::leanh::lean_dec(v___x_1885_);
                    v___x_1887_ = lean_nat_add(v___x_1824_, v_size_1825_);
                    v___x_1888_ = lean_nat_add(v___x_1887_, v_size_1843_);
                    crate::leanh::lean_dec(v___x_1887_);
                    crate::leanh::lean_inc_ref(v_r_1818_);
                    if v_isShared_1841_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1840_, 4, v_r_1818_);
                        crate::leanh::lean_ctor_set(v___x_1840_, 3, v_r_1830_);
                        crate::leanh::lean_ctor_set(v___x_1840_, 2, v_v_1816_);
                        crate::leanh::lean_ctor_set(v___x_1840_, 1, v_k_1815_);
                        crate::leanh::lean_ctor_set(v___x_1840_, 0, v___x_1888_);
                        v___x_1890_ = v___x_1840_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1903_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1888_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1815_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1816_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_r_1830_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_r_1818_);
                        v___x_1890_ = v_reuseFailAlloc_1903_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1854_ = lean_nat_add(v___x_1824_, v_size_1826_);
                crate::leanh::lean_dec(v_size_1826_);
                v___x_1855_ = lean_nat_add(v___x_1854_, v_size_1825_);
                crate::leanh::lean_dec(v___x_1854_);
                v___x_1867_ = lean_nat_add(v___x_1824_, v_size_1842_);
                if crate::leanh::lean_obj_tag(v_l_1846_) == 0 {
                    v_size_1877_ = crate::leanh::lean_ctor_get(v_l_1846_, 0);
                    crate::leanh::lean_inc(v_size_1877_);
                    v___y_1869_ = v_size_1877_;
                    state = 8;
                    continue;
                } else {
                    v___x_1878_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1869_ = v___x_1878_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1860_ = lean_nat_add(v___y_1858_, v___y_1859_);
                crate::leanh::lean_dec(v___y_1859_);
                crate::leanh::lean_dec(v___y_1858_);
                if v_isShared_1853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1852_, 4, v_r_1818_);
                    crate::leanh::lean_ctor_set(v___x_1852_, 3, v_r_1847_);
                    crate::leanh::lean_ctor_set(v___x_1852_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v___x_1852_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1860_);
                    v___x_1862_ = v___x_1852_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_r_1847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_r_1818_);
                    v___x_1862_ = v_reuseFailAlloc_1866_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1840_, 4, v___x_1862_);
                    crate::leanh::lean_ctor_set(v___x_1840_, 3, v___y_1857_);
                    crate::leanh::lean_ctor_set(v___x_1840_, 2, v_v_1845_);
                    crate::leanh::lean_ctor_set(v___x_1840_, 1, v_k_1844_);
                    crate::leanh::lean_ctor_set(v___x_1840_, 0, v___x_1855_);
                    v___x_1864_ = v___x_1840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_k_1844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_v_1845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 3, v___y_1857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 4, v___x_1862_);
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
                crate::leanh::lean_dec(v___y_1869_);
                crate::leanh::lean_dec(v___x_1867_);
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v_l_1846_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 3, v_l_1829_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 2, v_v_1828_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 1, v_k_1827_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1870_);
                    v___x_1872_ = v___x_1820_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1876_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_k_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_v_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_l_1829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_l_1846_);
                    v___x_1872_ = v_reuseFailAlloc_1876_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1873_ = lean_nat_add(v___x_1824_, v_size_1825_);
                if crate::leanh::lean_obj_tag(v_r_1847_) == 0 {
                    v_size_1874_ = crate::leanh::lean_ctor_get(v_r_1847_, 0);
                    crate::leanh::lean_inc(v_size_1874_);
                    v___y_1857_ = v___x_1872_;
                    v___y_1858_ = v___x_1873_;
                    v___y_1859_ = v_size_1874_;
                    state = 5;
                    continue;
                } else {
                    v___x_1875_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1857_ = v___x_1872_;
                    v___y_1858_ = v___x_1873_;
                    v___y_1859_ = v___x_1875_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1897_ = (!crate::leanh::lean_is_exclusive(v_r_1818_)) as u8;
                if v_isSharedCheck_1897_ == 0 {
                    v_unused_1898_ = crate::leanh::lean_ctor_get(v_r_1818_, 4);
                    crate::leanh::lean_dec(v_unused_1898_);
                    v_unused_1899_ = crate::leanh::lean_ctor_get(v_r_1818_, 3);
                    crate::leanh::lean_dec(v_unused_1899_);
                    v_unused_1900_ = crate::leanh::lean_ctor_get(v_r_1818_, 2);
                    crate::leanh::lean_dec(v_unused_1900_);
                    v_unused_1901_ = crate::leanh::lean_ctor_get(v_r_1818_, 1);
                    crate::leanh::lean_dec(v_unused_1901_);
                    v_unused_1902_ = crate::leanh::lean_ctor_get(v_r_1818_, 0);
                    crate::leanh::lean_dec(v_unused_1902_);
                    v___x_1892_ = v_r_1818_;
                    v_isShared_1893_ = v_isSharedCheck_1897_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1818_);
                    v___x_1892_ = crate::leanh::lean_box(0);
                    v_isShared_1893_ = v_isSharedCheck_1897_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1893_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1892_, 4, v___x_1890_);
                    crate::leanh::lean_ctor_set(v___x_1892_, 3, v_l_1829_);
                    crate::leanh::lean_ctor_set(v___x_1892_, 2, v_v_1828_);
                    crate::leanh::lean_ctor_set(v___x_1892_, 1, v_k_1827_);
                    crate::leanh::lean_ctor_set(v___x_1892_, 0, v___x_1886_);
                    v___x_1895_ = v___x_1892_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_k_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_v_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_l_1829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 4, v___x_1890_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1895_;
            }
            13 => {
                v___x_1917_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1911_);
                if v_isShared_1916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1915_, 3, v_r_1911_);
                    crate::leanh::lean_ctor_set(v___x_1915_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v___x_1915_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1824_);
                    v___x_1919_ = v___x_1915_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1923_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 3, v_r_1911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 4, v_r_1911_);
                    v___x_1919_ = v_reuseFailAlloc_1923_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v___x_1919_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 3, v_l_1910_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 2, v_v_1913_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 1, v_k_1912_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1917_);
                    v___x_1921_ = v___x_1820_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_l_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 4, v___x_1919_);
                    v___x_1921_ = v_reuseFailAlloc_1922_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1921_;
            }
            16 => {
                v_k_1933_ = crate::leanh::lean_ctor_get(v_r_1927_, 1);
                v_v_1934_ = crate::leanh::lean_ctor_get(v_r_1927_, 2);
                v_isSharedCheck_1948_ = (!crate::leanh::lean_is_exclusive(v_r_1927_)) as u8;
                if v_isSharedCheck_1948_ == 0 {
                    v_unused_1949_ = crate::leanh::lean_ctor_get(v_r_1927_, 4);
                    crate::leanh::lean_dec(v_unused_1949_);
                    v_unused_1950_ = crate::leanh::lean_ctor_get(v_r_1927_, 3);
                    crate::leanh::lean_dec(v_unused_1950_);
                    v_unused_1951_ = crate::leanh::lean_ctor_get(v_r_1927_, 0);
                    crate::leanh::lean_dec(v_unused_1951_);
                    v___x_1936_ = v_r_1927_;
                    v_isShared_1937_ = v_isSharedCheck_1948_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1934_);
                    crate::leanh::lean_inc(v_k_1933_);
                    crate::leanh::lean_dec(v_r_1927_);
                    v___x_1936_ = crate::leanh::lean_box(0);
                    v_isShared_1937_ = v_isSharedCheck_1948_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1938_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1936_, 4, v_l_1910_);
                    crate::leanh::lean_ctor_set(v___x_1936_, 3, v_l_1910_);
                    crate::leanh::lean_ctor_set(v___x_1936_, 2, v_v_1929_);
                    crate::leanh::lean_ctor_set(v___x_1936_, 1, v_k_1928_);
                    crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1824_);
                    v___x_1940_ = v___x_1936_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_l_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_l_1910_);
                    v___x_1940_ = v_reuseFailAlloc_1947_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1931_, 4, v_l_1910_);
                    crate::leanh::lean_ctor_set(v___x_1931_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v___x_1931_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v___x_1931_, 0, v___x_1824_);
                    v___x_1942_ = v___x_1931_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_l_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_l_1910_);
                    v___x_1942_ = v_reuseFailAlloc_1946_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v___x_1942_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 3, v___x_1940_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 2, v_v_1934_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 1, v_k_1933_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1938_);
                    v___x_1944_ = v___x_1820_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_k_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_v_1934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 3, v___x_1940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 4, v___x_1942_);
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
                v_size_1982_ = crate::leanh::lean_ctor_get(v_l_1969_, 0);
                v_k_1983_ = crate::leanh::lean_ctor_get(v_l_1969_, 1);
                v_v_1984_ = crate::leanh::lean_ctor_get(v_l_1969_, 2);
                v_l_1985_ = crate::leanh::lean_ctor_get(v_l_1969_, 3);
                v_r_1986_ = crate::leanh::lean_ctor_get(v_l_1969_, 4);
                v_size_1987_ = crate::leanh::lean_ctor_get(v_r_1970_, 0);
                v___x_1988_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1989_ = lean_nat_mul(v___x_1988_, v_size_1987_);
                v___x_1990_ = lean_nat_dec_lt(v_size_1982_, v___x_1989_);
                crate::leanh::lean_dec(v___x_1989_);
                if v___x_1990_ == 0 {
                    crate::leanh::lean_inc(v_r_1986_);
                    crate::leanh::lean_inc(v_l_1985_);
                    crate::leanh::lean_inc(v_v_1984_);
                    crate::leanh::lean_inc(v_k_1983_);
                    v_isSharedCheck_2018_ = (!crate::leanh::lean_is_exclusive(v_l_1969_)) as u8;
                    if v_isSharedCheck_2018_ == 0 {
                        v_unused_2019_ = crate::leanh::lean_ctor_get(v_l_1969_, 4);
                        crate::leanh::lean_dec(v_unused_2019_);
                        v_unused_2020_ = crate::leanh::lean_ctor_get(v_l_1969_, 3);
                        crate::leanh::lean_dec(v_unused_2020_);
                        v_unused_2021_ = crate::leanh::lean_ctor_get(v_l_1969_, 2);
                        crate::leanh::lean_dec(v_unused_2021_);
                        v_unused_2022_ = crate::leanh::lean_ctor_get(v_l_1969_, 1);
                        crate::leanh::lean_dec(v_unused_2022_);
                        v_unused_2023_ = crate::leanh::lean_ctor_get(v_l_1969_, 0);
                        crate::leanh::lean_dec(v_unused_2023_);
                        v___x_1992_ = v_l_1969_;
                        v_isShared_1993_ = v_isSharedCheck_2018_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1969_);
                        v___x_1992_ = crate::leanh::lean_box(0);
                        v_isShared_1993_ = v_isSharedCheck_2018_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1820_);
                    v___x_2024_ = lean_nat_add(v___x_1964_, v_size_1965_);
                    v___x_2025_ = lean_nat_add(v___x_2024_, v_size_1966_);
                    crate::leanh::lean_dec(v_size_1966_);
                    v___x_2026_ = lean_nat_add(v___x_2024_, v_size_1982_);
                    crate::leanh::lean_dec(v___x_2024_);
                    crate::leanh::lean_inc_ref(v_l_1817_);
                    if v_isShared_1981_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1980_, 4, v_l_1969_);
                        crate::leanh::lean_ctor_set(v___x_1980_, 3, v_l_1817_);
                        crate::leanh::lean_ctor_set(v___x_1980_, 2, v_v_1816_);
                        crate::leanh::lean_ctor_set(v___x_1980_, 1, v_k_1815_);
                        crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_2026_);
                        v___x_2028_ = v___x_1980_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2026_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1815_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1816_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_l_1817_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_l_1969_);
                        v___x_2028_ = v_reuseFailAlloc_2041_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1994_ = lean_nat_add(v___x_1964_, v_size_1965_);
                v___x_1995_ = lean_nat_add(v___x_1994_, v_size_1966_);
                crate::leanh::lean_dec(v_size_1966_);
                if crate::leanh::lean_obj_tag(v_l_1985_) == 0 {
                    v_size_2016_ = crate::leanh::lean_ctor_get(v_l_1985_, 0);
                    crate::leanh::lean_inc(v_size_2016_);
                    v___y_2008_ = v_size_2016_;
                    state = 29;
                    continue;
                } else {
                    v___x_2017_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2008_ = v___x_2017_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2000_ = lean_nat_add(v___y_1998_, v___y_1999_);
                crate::leanh::lean_dec(v___y_1999_);
                crate::leanh::lean_dec(v___y_1998_);
                if v_isShared_1993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1992_, 4, v_r_1970_);
                    crate::leanh::lean_ctor_set(v___x_1992_, 3, v_r_1986_);
                    crate::leanh::lean_ctor_set(v___x_1992_, 2, v_v_1968_);
                    crate::leanh::lean_ctor_set(v___x_1992_, 1, v_k_1967_);
                    crate::leanh::lean_ctor_set(v___x_1992_, 0, v___x_2000_);
                    v___x_2002_ = v___x_1992_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_1968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_r_1986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 4, v_r_1970_);
                    v___x_2002_ = v_reuseFailAlloc_2006_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1980_, 4, v___x_2002_);
                    crate::leanh::lean_ctor_set(v___x_1980_, 3, v___y_1997_);
                    crate::leanh::lean_ctor_set(v___x_1980_, 2, v_v_1984_);
                    crate::leanh::lean_ctor_set(v___x_1980_, 1, v_k_1983_);
                    crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_1995_);
                    v___x_2004_ = v___x_1980_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2005_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 3, v___y_1997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2005_, 4, v___x_2002_);
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
                crate::leanh::lean_dec(v___y_2008_);
                crate::leanh::lean_dec(v___x_1994_);
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v_l_1985_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_2009_);
                    v___x_2011_ = v___x_1820_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_l_1817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_l_1985_);
                    v___x_2011_ = v_reuseFailAlloc_2015_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2012_ = lean_nat_add(v___x_1964_, v_size_1987_);
                if crate::leanh::lean_obj_tag(v_r_1986_) == 0 {
                    v_size_2013_ = crate::leanh::lean_ctor_get(v_r_1986_, 0);
                    crate::leanh::lean_inc(v_size_2013_);
                    v___y_1997_ = v___x_2011_;
                    v___y_1998_ = v___x_2012_;
                    v___y_1999_ = v_size_2013_;
                    state = 26;
                    continue;
                } else {
                    v___x_2014_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1997_ = v___x_2011_;
                    v___y_1998_ = v___x_2012_;
                    v___y_1999_ = v___x_2014_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_2035_ = (!crate::leanh::lean_is_exclusive(v_l_1817_)) as u8;
                if v_isSharedCheck_2035_ == 0 {
                    v_unused_2036_ = crate::leanh::lean_ctor_get(v_l_1817_, 4);
                    crate::leanh::lean_dec(v_unused_2036_);
                    v_unused_2037_ = crate::leanh::lean_ctor_get(v_l_1817_, 3);
                    crate::leanh::lean_dec(v_unused_2037_);
                    v_unused_2038_ = crate::leanh::lean_ctor_get(v_l_1817_, 2);
                    crate::leanh::lean_dec(v_unused_2038_);
                    v_unused_2039_ = crate::leanh::lean_ctor_get(v_l_1817_, 1);
                    crate::leanh::lean_dec(v_unused_2039_);
                    v_unused_2040_ = crate::leanh::lean_ctor_get(v_l_1817_, 0);
                    crate::leanh::lean_dec(v_unused_2040_);
                    v___x_2030_ = v_l_1817_;
                    v_isShared_2031_ = v_isSharedCheck_2035_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1817_);
                    v___x_2030_ = crate::leanh::lean_box(0);
                    v_isShared_2031_ = v_isSharedCheck_2035_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2031_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2030_, 4, v_r_1970_);
                    crate::leanh::lean_ctor_set(v___x_2030_, 3, v___x_2028_);
                    crate::leanh::lean_ctor_set(v___x_2030_, 2, v_v_1968_);
                    crate::leanh::lean_ctor_set(v___x_2030_, 1, v_k_1967_);
                    crate::leanh::lean_ctor_set(v___x_2030_, 0, v___x_2025_);
                    v___x_2033_ = v___x_2030_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 3, v___x_2028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_r_1970_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2033_;
            }
            34 => {
                v_k_2055_ = crate::leanh::lean_ctor_get(v_l_2048_, 1);
                v_v_2056_ = crate::leanh::lean_ctor_get(v_l_2048_, 2);
                v_isSharedCheck_2070_ = (!crate::leanh::lean_is_exclusive(v_l_2048_)) as u8;
                if v_isSharedCheck_2070_ == 0 {
                    v_unused_2071_ = crate::leanh::lean_ctor_get(v_l_2048_, 4);
                    crate::leanh::lean_dec(v_unused_2071_);
                    v_unused_2072_ = crate::leanh::lean_ctor_get(v_l_2048_, 3);
                    crate::leanh::lean_dec(v_unused_2072_);
                    v_unused_2073_ = crate::leanh::lean_ctor_get(v_l_2048_, 0);
                    crate::leanh::lean_dec(v_unused_2073_);
                    v___x_2058_ = v_l_2048_;
                    v_isShared_2059_ = v_isSharedCheck_2070_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2056_);
                    crate::leanh::lean_inc(v_k_2055_);
                    crate::leanh::lean_dec(v_l_2048_);
                    v___x_2058_ = crate::leanh::lean_box(0);
                    v_isShared_2059_ = v_isSharedCheck_2070_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2060_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_2049_, 2);
                if v_isShared_2059_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2058_, 4, v_r_2049_);
                    crate::leanh::lean_ctor_set(v___x_2058_, 3, v_r_2049_);
                    crate::leanh::lean_ctor_set(v___x_2058_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v___x_2058_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v___x_2058_, 0, v___x_1964_);
                    v___x_2062_ = v___x_2058_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_r_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_r_2049_);
                    v___x_2062_ = v_reuseFailAlloc_2069_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_2049_);
                if v_isShared_2054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2053_, 3, v_r_2049_);
                    crate::leanh::lean_ctor_set(v___x_2053_, 0, v___x_1964_);
                    v___x_2064_ = v___x_2053_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_2051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_r_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_r_2049_);
                    v___x_2064_ = v_reuseFailAlloc_2068_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v___x_2064_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 3, v___x_2062_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 2, v_v_2056_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 1, v_k_2055_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_2060_);
                    v___x_2066_ = v___x_1820_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 3, v___x_2062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 4, v___x_2064_);
                    v___x_2066_ = v_reuseFailAlloc_2067_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2066_;
            }
            39 => {
                v___x_2083_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2082_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2081_, 4, v_l_2048_);
                    crate::leanh::lean_ctor_set(v___x_2081_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v___x_2081_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v___x_2081_, 0, v___x_1964_);
                    v___x_2085_ = v___x_2081_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_k_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_v_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_l_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_l_2048_);
                    v___x_2085_ = v_reuseFailAlloc_2089_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1820_, 4, v_r_2077_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 3, v___x_2085_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 2, v_v_2079_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 1, v_k_2078_);
                    crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_2083_);
                    v___x_2087_ = v___x_1820_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_2078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_2079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 3, v___x_2085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_r_2077_);
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
    mut v_init_2101_: *mut crate::leanh::LeanObject,
    mut v_x_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2102_) == 0 {
                    v_k_2103_ = crate::leanh::lean_ctor_get(v_x_2102_, 1);
                    crate::leanh::lean_inc(v_k_2103_);
                    v_v_2104_ = crate::leanh::lean_ctor_get(v_x_2102_, 2);
                    crate::leanh::lean_inc(v_v_2104_);
                    v_l_2105_ = crate::leanh::lean_ctor_get(v_x_2102_, 3);
                    crate::leanh::lean_inc(v_l_2105_);
                    v_r_2106_ = crate::leanh::lean_ctor_get(v_x_2102_, 4);
                    crate::leanh::lean_inc(v_r_2106_);
                    crate::leanh::lean_dec_ref_known(v_x_2102_, 5);
                    v___x_2107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_init_2101_, v_l_2105_);
                    if crate::leanh::lean_obj_tag(v___x_2107_) == 0 {
                        crate::leanh::lean_dec(v_r_2106_);
                        crate::leanh::lean_dec(v_v_2104_);
                        crate::leanh::lean_dec(v_k_2103_);
                        return v___x_2107_;
                    } else {
                        v_val_2108_ = crate::leanh::lean_ctor_get(v___x_2107_, 0);
                        crate::leanh::lean_inc(v_val_2108_);
                        crate::leanh::lean_dec_ref_known(v___x_2107_, 1);
                        v_a_2109_ = crate::leanh::lean_ctor_get(v_val_2108_, 0);
                        crate::leanh::lean_inc(v_a_2109_);
                        crate::leanh::lean_dec(v_val_2108_);
                        v___x_2110_ = l_Lean_LeanOptionValue_ofDataValue_x3f(v_v_2104_);
                        if crate::leanh::lean_obj_tag(v___x_2110_) == 0 {
                            crate::leanh::lean_dec(v_a_2109_);
                            crate::leanh::lean_dec(v_r_2106_);
                            crate::leanh::lean_dec(v_k_2103_);
                            v___x_2111_ = crate::leanh::lean_box(0);
                            return v___x_2111_;
                        } else {
                            v_val_2112_ = crate::leanh::lean_ctor_get(v___x_2110_, 0);
                            crate::leanh::lean_inc(v_val_2112_);
                            crate::leanh::lean_dec_ref_known(v___x_2110_, 1);
                            v___x_2113_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_2103_, v_val_2112_, v_a_2109_);
                            v_init_2101_ = v___x_2113_;
                            v_x_2102_ = v_r_2106_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v_init_2101_);
                    v___x_2116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2116_, 0, v___x_2115_);
                    return v___x_2116_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LeanOptions_fromOptions_x3f(
    mut v_options_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2118_ = crate::leanh::lean_ctor_get(v_options_2117_, 0);
                crate::leanh::lean_inc(v_map_2118_);
                crate::leanh::lean_dec_ref(v_options_2117_);
                v_values_2119_ = crate::leanh::lean_box(1);
                v___x_2120_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_LeanOptions_fromOptions_x3f_spec__1(v_values_2119_, v_map_2118_);
                if crate::leanh::lean_obj_tag(v___x_2120_) == 0 {
                    v___x_2121_ = crate::leanh::lean_box(0);
                    return v___x_2121_;
                } else {
                    v_val_2122_ = crate::leanh::lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2130_ = (!crate::leanh::lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2130_ == 0 {
                        v___x_2124_ = v___x_2120_;
                        v_isShared_2125_ = v_isSharedCheck_2130_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2122_);
                        crate::leanh::lean_dec(v___x_2120_);
                        v___x_2124_ = crate::leanh::lean_box(0);
                        v_isShared_2125_ = v_isSharedCheck_2130_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2126_ = crate::leanh::lean_ctor_get(v_val_2122_, 0);
                crate::leanh::lean_inc(v_a_2126_);
                crate::leanh::lean_dec(v_val_2122_);
                if v_isShared_2125_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2124_, 0, v_a_2126_);
                    v___x_2128_ = v___x_2124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2126_);
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
    mut v_00_u03b2_2131_: *mut crate::leanh::LeanObject,
    mut v_k_2132_: *mut crate::leanh::LeanObject,
    mut v_v_2133_: *mut crate::leanh::LeanObject,
    mut v_t_2134_: *mut crate::leanh::LeanObject,
    mut v_hl_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_LeanOptions_fromOptions_x3f_spec__0___redArg(v_k_2132_, v_v_2133_, v_t_2134_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_instFromJsonLeanOptions___lam__0(
    mut v___f_2137_: *mut crate::leanh::LeanObject,
    mut v_j_2138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_a_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2151_: u8 = 0;
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = l_Lean_NameMap_fromJson_x3f___redArg(v___f_2137_, v_j_2138_);
                if crate::leanh::lean_obj_tag(v___x_2139_) == 0 {
                    v_a_2140_ = crate::leanh::lean_ctor_get(v___x_2139_, 0);
                    v_isSharedCheck_2147_ = (!crate::leanh::lean_is_exclusive(v___x_2139_)) as u8;
                    if v_isSharedCheck_2147_ == 0 {
                        v___x_2142_ = v___x_2139_;
                        v_isShared_2143_ = v_isSharedCheck_2147_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2140_);
                        crate::leanh::lean_dec(v___x_2139_);
                        v___x_2142_ = crate::leanh::lean_box(0);
                        v_isShared_2143_ = v_isSharedCheck_2147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2148_ = crate::leanh::lean_ctor_get(v___x_2139_, 0);
                    v_isSharedCheck_2155_ = (!crate::leanh::lean_is_exclusive(v___x_2139_)) as u8;
                    if v_isSharedCheck_2155_ == 0 {
                        v___x_2150_ = v___x_2139_;
                        v_isShared_2151_ = v_isSharedCheck_2155_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2148_);
                        crate::leanh::lean_dec(v___x_2139_);
                        v___x_2150_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
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
                    v_reuseFailAlloc_2154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
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
    mut v___f_2159_: *mut crate::leanh::LeanObject,
    mut v_options_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_NameMap_toJson___redArg(v___f_2159_, v_options_2160_);
    return v___x_2161_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_LeanOptions(
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
    l_Lean_instInhabitedLeanOptions_default = _init_l_Lean_instInhabitedLeanOptions_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLeanOptions_default);
    l_Lean_instInhabitedLeanOptions = _init_l_Lean_instInhabitedLeanOptions();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLeanOptions);
    l_Lean_instEmptyCollectionLeanOptions = _init_l_Lean_instEmptyCollectionLeanOptions();
    crate::leanh::lean_mark_persistent(l_Lean_instEmptyCollectionLeanOptions);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_LeanOptions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_LeanOptions(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Util_LeanOptions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_LeanOptions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_LeanOptions(builtin);
}
