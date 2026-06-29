// Lean compiler output
// Module: Lake.Toml.Encode
// Imports: Lake.Util.FilePath Lake.Toml.Data.Value
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Lake::Toml::Data::Dict::l_Lake_Toml_RBDict_insert___redArg;
use crate::r#gen::Lake::Toml::Data::Value::{
    initialize_Lake_Toml_Data_Value, l_Lake_Toml_Value_table,
    runtime_initialize_Lake_Toml_Data_Value,
};
use crate::r#gen::Lake::Util::FilePath::{
    initialize_Lake_Util_FilePath, l_Lake_mkRelPathString, runtime_initialize_Lake_Util_FilePath,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_utf8_byte_size,
};
pub static l_Lake_instToTomlValue___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_instToTomlValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlValue___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlValue___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlFilePath___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlName___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlName___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlName___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlName: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlName___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlInt___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlNat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlFloat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlFloat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlFloat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFloat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__7_value:
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
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__9_value:
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
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlArrayValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToTomlArrayValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArrayValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArrayValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlArrayValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArrayValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instToTomlTable___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Lake_Toml_Value_table as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_instToTomlTable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlTable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToTomlTable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlTable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value: crate::leanh::LeanArrayObject<
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
static mut l_Lake_Toml_encodeArray_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_encodeArray_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_encodeArray_x3f___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_encodeArray_x3f___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value:
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
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_instSmartInsertTable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_instSmartInsertTable___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instSmartInsertTable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertTable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Toml_instSmartInsertTable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertTable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_instSmartInsertString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_instSmartInsertString___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instSmartInsertString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Toml_instSmartInsertString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_instToTomlString___lam__0(
    mut v_s_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ = crate::leanh::lean_box(0);
    v___x_305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_305_, 0, v___x_304_);
    crate::leanh::lean_ctor_set(v___x_305_, 1, v_s_303_);
    return v___x_305_;
}
pub unsafe fn l_Lake_instToTomlFilePath___lam__0(
    mut v_x_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = l_Lake_mkRelPathString(v_x_308_);
    v___x_310_ = crate::leanh::lean_box(0);
    v___x_311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_311_, 0, v___x_310_);
    crate::leanh::lean_ctor_set(v___x_311_, 1, v___x_309_);
    return v___x_311_;
}
pub unsafe fn l_Lake_instToTomlName___lam__0(
    mut v_x_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: u8 = 0;
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = 1;
    v___x_316_ = l_Lean_Name_toString(v_x_314_, v___x_315_);
    v___x_317_ = crate::leanh::lean_box(0);
    v___x_318_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
    crate::leanh::lean_ctor_set(v___x_318_, 1, v___x_316_);
    return v___x_318_;
}
pub unsafe fn l_Lake_instToTomlInt___lam__0(
    mut v_n_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = crate::leanh::lean_box(0);
    v___x_323_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_323_, 0, v___x_322_);
    crate::leanh::lean_ctor_set(v___x_323_, 1, v_n_321_);
    return v___x_323_;
}
pub unsafe fn l_Lake_instToTomlNat___lam__0(
    mut v_n_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = crate::leanh::lean_box(0);
    v___x_328_ = lean_nat_to_int(v_n_326_);
    v___x_329_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_329_, 0, v___x_327_);
    crate::leanh::lean_ctor_set(v___x_329_, 1, v___x_328_);
    return v___x_329_;
}
pub unsafe fn l_Lake_instToTomlFloat___lam__0(mut v_n_332_: f64) -> *mut crate::leanh::LeanObject {
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = crate::leanh::lean_box(0);
    v___x_334_ = crate::leanh::lean_alloc_ctor(2, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_334_, 0, v___x_333_);
    crate::leanh::lean_ctor_set_float(
        v___x_334_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_n_332_,
    );
    return v___x_334_;
}
pub unsafe fn l_Lake_instToTomlFloat___lam__0___boxed(
    mut v_n_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_336_: f64 = 0.0;
    let mut v_res_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_336_ = crate::leanh::lean_unbox_float(v_n_335_);
    crate::leanh::lean_dec_ref(v_n_335_);
    v_res_337_ = l_Lake_instToTomlFloat___lam__0(v_n_boxed_336_);
    return v_res_337_;
}
pub unsafe fn l_Lake_instToTomlBool___lam__0(mut v_b_340_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = crate::leanh::lean_box(0);
    v___x_342_ = crate::leanh::lean_alloc_ctor(3, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_342_, 0, v___x_341_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_342_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_b_340_,
    );
    return v___x_342_;
}
pub unsafe fn l_Lake_instToTomlBool___lam__0___boxed(
    mut v_b_343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_344_: u8 = 0;
    let mut v_res_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_344_ = (crate::leanh::lean_unbox(v_b_343_) as u8);
    v_res_345_ = l_Lake_instToTomlBool___lam__0(v_b_boxed_344_);
    return v_res_345_;
}
pub unsafe fn l_Lake_instToTomlArray___redArg___lam__0(
    mut v_inst_348_: *mut crate::leanh::LeanObject,
    mut v_x_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_apply_1(v_inst_348_, v_x_349_);
    return v___x_350_;
}
pub unsafe fn l_Lake_instToTomlArray___redArg___lam__1(
    mut v___f_370_: *mut crate::leanh::LeanObject,
    mut v_x_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_374_: usize = 0;
    let mut v___x_375_: usize = 0;
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = crate::leanh::lean_box(0);
    v___x_373_ = l_Lake_instToTomlArray___redArg___lam__1___closed__9;
    v_sz_374_ = lean_array_size(v_x_371_);
    v___x_375_ = 0usize;
    v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_373_,
        v___f_370_,
        v_sz_374_,
        v___x_375_,
        v_x_371_,
    );
    v___x_377_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_377_, 0, v___x_372_);
    crate::leanh::lean_ctor_set(v___x_377_, 1, v___x_376_);
    return v___x_377_;
}
pub unsafe fn l_Lake_instToTomlArray___redArg(
    mut v_inst_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_379_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTomlArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_379_, 0, v_inst_378_);
    v___f_380_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToTomlArray___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_380_, 0, v___f_379_);
    return v___f_380_;
}
pub unsafe fn l_Lake_instToTomlArray(
    mut v_00_u03b1_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = l_Lake_instToTomlArray___redArg(v_inst_382_);
    return v___x_383_;
}
pub unsafe fn l_Lake_instToTomlArrayValue___lam__0(
    mut v_x_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = crate::leanh::lean_box(0);
    v___x_386_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_386_, 0, v___x_385_);
    crate::leanh::lean_ctor_set(v___x_386_, 1, v_x_384_);
    return v___x_386_;
}
pub unsafe fn l_Lake_instToToml_x3fOfToToml___redArg___lam__0(
    mut v_inst_392_: *mut crate::leanh::LeanObject,
    mut v_v_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = crate::leanh::lean_apply_1(v_inst_392_, v_v_393_);
    v___x_395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_395_, 0, v___x_394_);
    return v___x_395_;
}
pub unsafe fn l_Lake_instToToml_x3fOfToToml___redArg(
    mut v_inst_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_397_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_397_, 0, v_inst_396_);
    return v___f_397_;
}
pub unsafe fn l_Lake_instToToml_x3fOfToToml(
    mut v_00_u03b1_398_: *mut crate::leanh::LeanObject,
    mut v_inst_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_400_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_400_, 0, v_inst_399_);
    return v___f_400_;
}
pub unsafe fn l_Lake_Toml_encodeArray_x3f___redArg___lam__0(
    mut v_inst_401_: *mut crate::leanh::LeanObject,
    mut v_x1_402_: *mut crate::leanh::LeanObject,
    mut v_x2_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_410_: u8 = 0;
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x1_402_) == 0 {
                    crate::leanh::lean_dec(v_x2_403_);
                    crate::leanh::lean_dec_ref(v_inst_401_);
                    return v_x1_402_;
                } else {
                    v_val_404_ = crate::leanh::lean_ctor_get(v_x1_402_, 0);
                    crate::leanh::lean_inc(v_val_404_);
                    crate::leanh::lean_dec_ref_known(v_x1_402_, 1);
                    v___x_405_ = crate::leanh::lean_apply_1(v_inst_401_, v_x2_403_);
                    if crate::leanh::lean_obj_tag(v___x_405_) == 0 {
                        crate::leanh::lean_dec(v_val_404_);
                        v___x_406_ = crate::leanh::lean_box(0);
                        return v___x_406_;
                    } else {
                        v_val_407_ = crate::leanh::lean_ctor_get(v___x_405_, 0);
                        v_isSharedCheck_415_ = (!crate::leanh::lean_is_exclusive(v___x_405_)) as u8;
                        if v_isSharedCheck_415_ == 0 {
                            v___x_409_ = v___x_405_;
                            v_isShared_410_ = v_isSharedCheck_415_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_407_);
                            crate::leanh::lean_dec(v___x_405_);
                            v___x_409_ = crate::leanh::lean_box(0);
                            v_isShared_410_ = v_isSharedCheck_415_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_411_ = lean_array_push(v_val_404_, v_val_407_);
                if v_isShared_410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_409_, 0, v___x_411_);
                    v___x_413_ = v___x_409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
                    v___x_413_ = v_reuseFailAlloc_414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_encodeArray_x3f___redArg(
    mut v_inst_420_: *mut crate::leanh::LeanObject,
    mut v_as_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    v___x_422_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_423_ = l_Lake_Toml_encodeArray_x3f___redArg___closed__1;
    v___x_424_ = lean_array_get_size(v_as_421_);
    v___x_425_ = l_Lake_instToTomlArray___redArg___lam__1___closed__9;
    v___x_426_ = lean_nat_dec_lt(v___x_422_, v___x_424_);
    if v___x_426_ == 0 {
        crate::leanh::lean_dec_ref(v_as_421_);
        crate::leanh::lean_dec_ref(v_inst_420_);
        return v___x_423_;
    } else {
        let mut v___f_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_428_: u8 = 0;
        v___f_427_ = crate::leanh::lean_alloc_closure(
            l_Lake_Toml_encodeArray_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_427_, 0, v_inst_420_);
        v___x_428_ = lean_nat_dec_le(v___x_424_, v___x_424_);
        if v___x_428_ == 0 {
            if v___x_426_ == 0 {
                crate::leanh::lean_dec_ref(v___f_427_);
                crate::leanh::lean_dec_ref(v_as_421_);
                return v___x_423_;
            } else {
                let mut v___x_429_: usize = 0;
                let mut v___x_430_: usize = 0;
                let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_429_ = 0usize;
                v___x_430_ = lean_usize_of_nat(v___x_424_);
                v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_425_,
                    v___f_427_,
                    v_as_421_,
                    v___x_429_,
                    v___x_430_,
                    v___x_423_,
                );
                return v___x_431_;
            }
        } else {
            let mut v___x_432_: usize = 0;
            let mut v___x_433_: usize = 0;
            let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_432_ = 0usize;
            v___x_433_ = lean_usize_of_nat(v___x_424_);
            v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_425_,
                v___f_427_,
                v_as_421_,
                v___x_432_,
                v___x_433_,
                v___x_423_,
            );
            return v___x_434_;
        }
    }
}
pub unsafe fn l_Lake_Toml_encodeArray_x3f(
    mut v_00_u03b1_435_: *mut crate::leanh::LeanObject,
    mut v_inst_436_: *mut crate::leanh::LeanObject,
    mut v_as_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_436_, v_as_437_);
    return v___x_438_;
}
pub unsafe fn l_Lake_instToToml_x3fArray___redArg___lam__0(
    mut v_inst_439_: *mut crate::leanh::LeanObject,
    mut v_as_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_441_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_439_, v_as_440_);
                if crate::leanh::lean_obj_tag(v___x_441_) == 0 {
                    v___x_442_ = crate::leanh::lean_box(0);
                    return v___x_442_;
                } else {
                    v_val_443_ = crate::leanh::lean_ctor_get(v___x_441_, 0);
                    v_isSharedCheck_452_ = (!crate::leanh::lean_is_exclusive(v___x_441_)) as u8;
                    if v_isSharedCheck_452_ == 0 {
                        v___x_445_ = v___x_441_;
                        v_isShared_446_ = v_isSharedCheck_452_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_443_);
                        crate::leanh::lean_dec(v___x_441_);
                        v___x_445_ = crate::leanh::lean_box(0);
                        v_isShared_446_ = v_isSharedCheck_452_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_447_ = crate::leanh::lean_box(0);
                v___x_448_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_448_, 0, v___x_447_);
                crate::leanh::lean_ctor_set(v___x_448_, 1, v_val_443_);
                if v_isShared_446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_445_, 0, v___x_448_);
                    v___x_450_ = v___x_445_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
                    v___x_450_ = v_reuseFailAlloc_451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instToToml_x3fArray___redArg(
    mut v_inst_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_454_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_454_, 0, v_inst_453_);
    return v___f_454_;
}
pub unsafe fn l_Lake_instToToml_x3fArray(
    mut v_00_u03b1_455_: *mut crate::leanh::LeanObject,
    mut v_inst_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_457_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_457_, 0, v_inst_456_);
    return v___f_457_;
}
pub unsafe fn l_Lake_instToToml_x3fOption___redArg___lam__0(
    mut v_inst_458_: *mut crate::leanh::LeanObject,
    mut v_x_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_459_) == 0 {
        let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_458_);
        v___x_460_ = crate::leanh::lean_box(0);
        return v___x_460_;
    } else {
        let mut v_val_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_461_ = crate::leanh::lean_ctor_get(v_x_459_, 0);
        crate::leanh::lean_inc(v_val_461_);
        crate::leanh::lean_dec_ref_known(v_x_459_, 1);
        v___x_462_ = crate::leanh::lean_apply_1(v_inst_458_, v_val_461_);
        return v___x_462_;
    }
}
pub unsafe fn l_Lake_instToToml_x3fOption___redArg(
    mut v_inst_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_464_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_464_, 0, v_inst_463_);
    return v___f_464_;
}
pub unsafe fn l_Lake_instToToml_x3fOption(
    mut v_00_u03b1_465_: *mut crate::leanh::LeanObject,
    mut v_inst_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_467_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_467_, 0, v_inst_466_);
    return v___f_467_;
}
pub unsafe fn l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(
    mut v_inst_468_: *mut crate::leanh::LeanObject,
    mut v_x_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_469_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_468_);
                    v___x_470_ = crate::leanh::lean_box(0);
                    return v___x_470_;
                } else {
                    v_val_471_ = crate::leanh::lean_ctor_get(v_x_469_, 0);
                    v_isSharedCheck_479_ = (!crate::leanh::lean_is_exclusive(v_x_469_)) as u8;
                    if v_isSharedCheck_479_ == 0 {
                        v___x_473_ = v_x_469_;
                        v_isShared_474_ = v_isSharedCheck_479_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_471_);
                        crate::leanh::lean_dec(v_x_469_);
                        v___x_473_ = crate::leanh::lean_box(0);
                        v_isShared_474_ = v_isSharedCheck_479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_475_ = crate::leanh::lean_apply_1(v_inst_468_, v_val_471_);
                if v_isShared_474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_475_);
                    v___x_477_ = v___x_473_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
                    v___x_477_ = v_reuseFailAlloc_478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instToToml_x3fOptionOfToToml___redArg(
    mut v_inst_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_481_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_481_, 0, v_inst_480_);
    return v___f_481_;
}
pub unsafe fn l_Lake_instToToml_x3fOptionOfToToml(
    mut v_00_u03b1_482_: *mut crate::leanh::LeanObject,
    mut v_inst_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_484_ = crate::leanh::lean_alloc_closure(
        l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_484_, 0, v_inst_483_);
    return v___f_484_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(
    mut v_inst_486_: *mut crate::leanh::LeanObject,
    mut v_k_487_: *mut crate::leanh::LeanObject,
    mut v_v_488_: *mut crate::leanh::LeanObject,
    mut v_t_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = crate::leanh::lean_apply_1(v_inst_486_, v_v_488_);
    if crate::leanh::lean_obj_tag(v___x_490_) == 1 {
        let mut v_val_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_491_ = crate::leanh::lean_ctor_get(v___x_490_, 0);
        crate::leanh::lean_inc(v_val_491_);
        crate::leanh::lean_dec_ref_known(v___x_490_, 1);
        v___x_492_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_493_ = l_Lake_Toml_RBDict_insert___redArg(v___x_492_, v_k_487_, v_val_491_, v_t_489_);
        return v___x_493_;
    } else {
        crate::leanh::lean_dec(v___x_490_);
        crate::leanh::lean_dec(v_k_487_);
        return v_t_489_;
    }
}
pub unsafe fn l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(
    mut v_inst_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_495_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_495_, 0, v_inst_494_);
    return v___f_495_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertOfToToml_x3f(
    mut v_00_u03b1_496_: *mut crate::leanh::LeanObject,
    mut v_inst_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_498_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_498_, 0, v_inst_497_);
    return v___f_498_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertTable___lam__0(
    mut v_k_499_: *mut crate::leanh::LeanObject,
    mut v_v_500_: *mut crate::leanh::LeanObject,
    mut v_t_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_items_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    v_items_502_ = crate::leanh::lean_ctor_get(v_v_500_, 0);
    v___x_503_ = lean_array_get_size(v_items_502_);
    v___x_504_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
    if v___x_505_ == 0 {
        let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_506_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_507_ = crate::leanh::lean_box(0);
        v___x_508_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_508_, 0, v___x_507_);
        crate::leanh::lean_ctor_set(v___x_508_, 1, v_v_500_);
        v___x_509_ = l_Lake_Toml_RBDict_insert___redArg(v___x_506_, v_k_499_, v___x_508_, v_t_501_);
        return v___x_509_;
    } else {
        crate::leanh::lean_dec_ref(v_v_500_);
        crate::leanh::lean_dec(v_k_499_);
        return v_t_501_;
    }
}
pub unsafe fn l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(
    mut v_inst_512_: *mut crate::leanh::LeanObject,
    mut v_k_513_: *mut crate::leanh::LeanObject,
    mut v_v_514_: *mut crate::leanh::LeanObject,
    mut v_t_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    v___x_516_ = lean_array_get_size(v_v_514_);
    v___x_517_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_518_ = lean_nat_dec_eq(v___x_516_, v___x_517_);
    if v___x_518_ == 0 {
        let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_519_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_520_ = crate::leanh::lean_apply_1(v_inst_512_, v_v_514_);
        v___x_521_ = l_Lake_Toml_RBDict_insert___redArg(v___x_519_, v_k_513_, v___x_520_, v_t_515_);
        return v___x_521_;
    } else {
        crate::leanh::lean_dec_ref(v_v_514_);
        crate::leanh::lean_dec(v_k_513_);
        crate::leanh::lean_dec_ref(v_inst_512_);
        return v_t_515_;
    }
}
pub unsafe fn l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(
    mut v_inst_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_523_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_523_, 0, v_inst_522_);
    return v___f_523_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertArrayOfToToml(
    mut v_00_u03b1_524_: *mut crate::leanh::LeanObject,
    mut v_inst_525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_526_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_526_, 0, v_inst_525_);
    return v___f_526_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertString___lam__0(
    mut v_k_527_: *mut crate::leanh::LeanObject,
    mut v_v_528_: *mut crate::leanh::LeanObject,
    mut v_t_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    v___x_530_ = lean_string_utf8_byte_size(v_v_528_);
    v___x_531_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_532_ = lean_nat_dec_eq(v___x_530_, v___x_531_);
    if v___x_532_ == 0 {
        let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_533_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_534_ = crate::leanh::lean_box(0);
        v___x_535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_535_, 0, v___x_534_);
        crate::leanh::lean_ctor_set(v___x_535_, 1, v_v_528_);
        v___x_536_ = l_Lake_Toml_RBDict_insert___redArg(v___x_533_, v_k_527_, v___x_535_, v_t_529_);
        return v___x_536_;
    } else {
        crate::leanh::lean_dec_ref(v_v_528_);
        crate::leanh::lean_dec(v_k_527_);
        return v_t_529_;
    }
}
pub unsafe fn l_Lake_Toml_Table_insert___redArg(
    mut v_enc_539_: *mut crate::leanh::LeanObject,
    mut v_k_540_: *mut crate::leanh::LeanObject,
    mut v_v_541_: *mut crate::leanh::LeanObject,
    mut v_t_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
    v___x_544_ = crate::leanh::lean_apply_1(v_enc_539_, v_v_541_);
    v___x_545_ = l_Lake_Toml_RBDict_insert___redArg(v___x_543_, v_k_540_, v___x_544_, v_t_542_);
    return v___x_545_;
}
pub unsafe fn l_Lake_Toml_Table_insert(
    mut v_00_u03b1_546_: *mut crate::leanh::LeanObject,
    mut v_enc_547_: *mut crate::leanh::LeanObject,
    mut v_k_548_: *mut crate::leanh::LeanObject,
    mut v_v_549_: *mut crate::leanh::LeanObject,
    mut v_t_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
    v___x_552_ = crate::leanh::lean_apply_1(v_enc_547_, v_v_549_);
    v___x_553_ = l_Lake_Toml_RBDict_insert___redArg(v___x_551_, v_k_548_, v___x_552_, v_t_550_);
    return v___x_553_;
}
pub unsafe fn l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(
    mut v_inst_554_: *mut crate::leanh::LeanObject,
    mut v_k_555_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_556_: *mut crate::leanh::LeanObject,
    mut v_t_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_v_x3f_556_) == 0 {
        crate::leanh::lean_dec(v_k_555_);
        crate::leanh::lean_dec_ref(v_inst_554_);
        return v_t_557_;
    } else {
        let mut v_val_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_558_ = crate::leanh::lean_ctor_get(v_v_x3f_556_, 0);
        crate::leanh::lean_inc(v_val_558_);
        crate::leanh::lean_dec_ref_known(v_v_x3f_556_, 1);
        v___x_559_ = crate::leanh::lean_apply_1(v_inst_554_, v_val_558_);
        v___x_560_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_561_ = l_Lake_Toml_RBDict_insert___redArg(v___x_560_, v_k_555_, v___x_559_, v_t_557_);
        return v___x_561_;
    }
}
pub unsafe fn l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(
    mut v_inst_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_563_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_563_, 0, v_inst_562_);
    return v___f_563_;
}
pub unsafe fn l_Lake_Toml_Table_instSmartInsertOptionOfToToml(
    mut v_00_u03b1_564_: *mut crate::leanh::LeanObject,
    mut v_inst_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_566_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_566_, 0, v_inst_565_);
    return v___f_566_;
}
pub unsafe fn l_Lake_Toml_Table_smartInsert___redArg(
    mut v_inst_567_: *mut crate::leanh::LeanObject,
    mut v_k_568_: *mut crate::leanh::LeanObject,
    mut v_v_569_: *mut crate::leanh::LeanObject,
    mut v_t_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = crate::leanh::lean_apply_3(v_inst_567_, v_k_568_, v_v_569_, v_t_570_);
    return v___x_571_;
}
pub unsafe fn l_Lake_Toml_Table_smartInsert(
    mut v_00_u03b1_572_: *mut crate::leanh::LeanObject,
    mut v_inst_573_: *mut crate::leanh::LeanObject,
    mut v_k_574_: *mut crate::leanh::LeanObject,
    mut v_v_575_: *mut crate::leanh::LeanObject,
    mut v_t_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_577_ = crate::leanh::lean_apply_3(v_inst_573_, v_k_574_, v_v_575_, v_t_576_);
    return v___x_577_;
}
pub unsafe fn l_Lake_Toml_Table_insertD___redArg(
    mut v_enc_578_: *mut crate::leanh::LeanObject,
    mut v_inst_579_: *mut crate::leanh::LeanObject,
    mut v_k_580_: *mut crate::leanh::LeanObject,
    mut v_v_581_: *mut crate::leanh::LeanObject,
    mut v_default_582_: *mut crate::leanh::LeanObject,
    mut v_t_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    crate::leanh::lean_inc(v_v_581_);
    v___x_584_ = crate::leanh::lean_apply_2(v_inst_579_, v_v_581_, v_default_582_);
    v___x_585_ = (crate::leanh::lean_unbox(v___x_584_) as u8);
    if v___x_585_ == 0 {
        let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_586_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_587_ = crate::leanh::lean_apply_1(v_enc_578_, v_v_581_);
        v___x_588_ = l_Lake_Toml_RBDict_insert___redArg(v___x_586_, v_k_580_, v___x_587_, v_t_583_);
        return v___x_588_;
    } else {
        crate::leanh::lean_dec(v_v_581_);
        crate::leanh::lean_dec(v_k_580_);
        crate::leanh::lean_dec_ref(v_enc_578_);
        return v_t_583_;
    }
}
pub unsafe fn l_Lake_Toml_Table_insertD(
    mut v_00_u03b1_589_: *mut crate::leanh::LeanObject,
    mut v_enc_590_: *mut crate::leanh::LeanObject,
    mut v_inst_591_: *mut crate::leanh::LeanObject,
    mut v_k_592_: *mut crate::leanh::LeanObject,
    mut v_v_593_: *mut crate::leanh::LeanObject,
    mut v_default_594_: *mut crate::leanh::LeanObject,
    mut v_t_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    crate::leanh::lean_inc(v_v_593_);
    v___x_596_ = crate::leanh::lean_apply_2(v_inst_591_, v_v_593_, v_default_594_);
    v___x_597_ = (crate::leanh::lean_unbox(v___x_596_) as u8);
    if v___x_597_ == 0 {
        let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_598_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_599_ = crate::leanh::lean_apply_1(v_enc_590_, v_v_593_);
        v___x_600_ = l_Lake_Toml_RBDict_insert___redArg(v___x_598_, v_k_592_, v___x_599_, v_t_595_);
        return v___x_600_;
    } else {
        crate::leanh::lean_dec(v_v_593_);
        crate::leanh::lean_dec(v_k_592_);
        crate::leanh::lean_dec_ref(v_enc_590_);
        return v_t_595_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Encode(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Encode(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Encode(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Toml_Data_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Encode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Encode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Encode(builtin);
}
