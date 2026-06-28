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
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_float, lean_unsigned_to_nat,
};
pub static l_Lake_instToTomlValue___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_instToTomlValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlValue___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlString___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlFilePath___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlFilePath___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlName___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlName___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlName___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlName: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlName___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlInt___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlInt___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlNat___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlNat___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlFloat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFloat___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlFloat: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlFloat___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instToTomlBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instToTomlBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlBool___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlBool___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArray___redArg___lam__1___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instToTomlArray___redArg___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArray___redArg___lam__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_instToTomlArrayValue___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instToTomlArrayValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToTomlArrayValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArrayValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlArrayValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlArrayValue___closed__0_value) as *mut LeanObject;
pub static l_Lake_instToTomlTable___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_Value_table as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_instToTomlTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlTable___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToTomlTable: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToTomlTable___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_Toml_encodeArray_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_encodeArray_x3f___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_encodeArray_x3f___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_Toml_encodeArray_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_encodeArray_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_instSmartInsertTable___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_instSmartInsertTable___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instSmartInsertTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertTable___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instSmartInsertTable: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertTable___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_instSmartInsertString___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_instSmartInsertString___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instSmartInsertString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instSmartInsertString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instSmartInsertString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_instToTomlString___lam__0(mut v_s_303_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    v___x_304_ = lean_box(0);
    v___x_305_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_305_, 0, v___x_304_);
    lean_ctor_set(v___x_305_, 1, v_s_303_);
    return v___x_305_;
}
pub unsafe fn l_Lake_instToTomlFilePath___lam__0(mut v_x_308_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    v___x_309_ = l_Lake_mkRelPathString(v_x_308_);
    v___x_310_ = lean_box(0);
    v___x_311_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_311_, 0, v___x_310_);
    lean_ctor_set(v___x_311_, 1, v___x_309_);
    return v___x_311_;
}
pub unsafe fn l_Lake_instToTomlName___lam__0(mut v_x_314_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_315_: u8 = 0;
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_315_ = 1;
    v___x_316_ = l_Lean_Name_toString(v_x_314_, v___x_315_);
    v___x_317_ = lean_box(0);
    v___x_318_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_318_, 0, v___x_317_);
    lean_ctor_set(v___x_318_, 1, v___x_316_);
    return v___x_318_;
}
pub unsafe fn l_Lake_instToTomlInt___lam__0(mut v_n_321_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_box(0);
    v___x_323_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_323_, 0, v___x_322_);
    lean_ctor_set(v___x_323_, 1, v_n_321_);
    return v___x_323_;
}
pub unsafe fn l_Lake_instToTomlNat___lam__0(mut v_n_326_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_box(0);
    v___x_328_ = lean_nat_to_int(v_n_326_);
    v___x_329_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_329_, 0, v___x_327_);
    lean_ctor_set(v___x_329_, 1, v___x_328_);
    return v___x_329_;
}
pub unsafe fn l_Lake_instToTomlFloat___lam__0(mut v_n_332_: f64) -> *mut LeanObject {
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    v___x_333_ = lean_box(0);
    v___x_334_ = lean_alloc_ctor(2, 1, (8) as u32);
    lean_ctor_set(v___x_334_, 0, v___x_333_);
    lean_ctor_set_float(
        v___x_334_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_n_332_,
    );
    return v___x_334_;
}
pub unsafe fn l_Lake_instToTomlFloat___lam__0___boxed(
    mut v_n_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_336_: f64 = 0.0;
    let mut v_res_337_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_336_ = lean_unbox_float(v_n_335_);
    lean_dec_ref(v_n_335_);
    v_res_337_ = l_Lake_instToTomlFloat___lam__0(v_n_boxed_336_);
    return v_res_337_;
}
pub unsafe fn l_Lake_instToTomlBool___lam__0(mut v_b_340_: u8) -> *mut LeanObject {
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_341_ = lean_box(0);
    v___x_342_ = lean_alloc_ctor(3, 1, (1) as u32);
    lean_ctor_set(v___x_342_, 0, v___x_341_);
    lean_ctor_set_uint8(
        v___x_342_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_b_340_,
    );
    return v___x_342_;
}
pub unsafe fn l_Lake_instToTomlBool___lam__0___boxed(
    mut v_b_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_344_: u8 = 0;
    let mut v_res_345_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_344_ = (lean_unbox(v_b_343_) as u8);
    v_res_345_ = l_Lake_instToTomlBool___lam__0(v_b_boxed_344_);
    return v_res_345_;
}
pub unsafe fn l_Lake_instToTomlArray___redArg___lam__0(
    mut v_inst_348_: *mut LeanObject,
    mut v_x_349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_apply_1(v_inst_348_, v_x_349_);
    return v___x_350_;
}
pub unsafe fn l_Lake_instToTomlArray___redArg___lam__1(
    mut v___f_370_: *mut LeanObject,
    mut v_x_371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_374_: usize = 0;
    let mut v___x_375_: usize = 0;
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = lean_box(0);
    v___x_373_ = l_Lake_instToTomlArray___redArg___lam__1___closed__9;
    v_sz_374_ = lean_array_size(v_x_371_);
    v___x_375_ = 0usize;
    v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_373_,
        v___f_370_,
        v_sz_374_,
        v___x_375_,
        v_x_371_,
    );
    v___x_377_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_377_, 0, v___x_372_);
    lean_ctor_set(v___x_377_, 1, v___x_376_);
    return v___x_377_;
}
pub unsafe fn l_Lake_instToTomlArray___redArg(mut v_inst_378_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_380_: *mut LeanObject = core::ptr::null_mut();
    v___f_379_ = lean_alloc_closure(
        l_Lake_instToTomlArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_379_, 0, v_inst_378_);
    v___f_380_ = lean_alloc_closure(
        l_Lake_instToTomlArray___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_380_, 0, v___f_379_);
    return v___f_380_;
}
pub unsafe fn l_Lake_instToTomlArray(
    mut v_00_u03b1_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_383_ = l_Lake_instToTomlArray___redArg(v_inst_382_);
    return v___x_383_;
}
pub unsafe fn l_Lake_instToTomlArrayValue___lam__0(
    mut v_x_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v___x_385_ = lean_box(0);
    v___x_386_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_386_, 0, v___x_385_);
    lean_ctor_set(v___x_386_, 1, v_x_384_);
    return v___x_386_;
}
pub unsafe fn l_Lake_instToToml_x3fOfToToml___redArg___lam__0(
    mut v_inst_392_: *mut LeanObject,
    mut v_v_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = lean_apply_1(v_inst_392_, v_v_393_);
    v___x_395_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_395_, 0, v___x_394_);
    return v___x_395_;
}
pub unsafe fn l_Lake_instToToml_x3fOfToToml___redArg(
    mut v_inst_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_397_: *mut LeanObject = core::ptr::null_mut();
    v___f_397_ = lean_alloc_closure(
        l_Lake_instToToml_x3fOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_397_, 0, v_inst_396_);
    return v___f_397_;
}
pub unsafe fn l_Lake_instToToml_x3fOfToToml(
    mut v_00_u03b1_398_: *mut LeanObject,
    mut v_inst_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_400_: *mut LeanObject = core::ptr::null_mut();
    v___f_400_ = lean_alloc_closure(
        l_Lake_instToToml_x3fOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_400_, 0, v_inst_399_);
    return v___f_400_;
}
pub unsafe fn l_Lake_Toml_encodeArray_x3f___redArg___lam__0(
    mut v_inst_401_: *mut LeanObject,
    mut v_x1_402_: *mut LeanObject,
    mut v_x2_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_410_: u8 = 0;
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x1_402_) == 0 {
                    lean_dec(v_x2_403_);
                    lean_dec_ref(v_inst_401_);
                    return v_x1_402_;
                } else {
                    v_val_404_ = lean_ctor_get(v_x1_402_, 0);
                    lean_inc(v_val_404_);
                    lean_dec_ref_known(v_x1_402_, 1);
                    v___x_405_ = lean_apply_1(v_inst_401_, v_x2_403_);
                    if lean_obj_tag(v___x_405_) == 0 {
                        lean_dec(v_val_404_);
                        v___x_406_ = lean_box(0);
                        return v___x_406_;
                    } else {
                        v_val_407_ = lean_ctor_get(v___x_405_, 0);
                        v_isSharedCheck_415_ = (!lean_is_exclusive(v___x_405_)) as u8;
                        if v_isSharedCheck_415_ == 0 {
                            v___x_409_ = v___x_405_;
                            v_isShared_410_ = v_isSharedCheck_415_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_407_);
                            lean_dec(v___x_405_);
                            v___x_409_ = lean_box(0);
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
                    lean_ctor_set(v___x_409_, 0, v___x_411_);
                    v___x_413_ = v___x_409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
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
    mut v_inst_420_: *mut LeanObject,
    mut v_as_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    v___x_422_ = lean_unsigned_to_nat(0);
    v___x_423_ = l_Lake_Toml_encodeArray_x3f___redArg___closed__1;
    v___x_424_ = lean_array_get_size(v_as_421_);
    v___x_425_ = l_Lake_instToTomlArray___redArg___lam__1___closed__9;
    v___x_426_ = lean_nat_dec_lt(v___x_422_, v___x_424_);
    if v___x_426_ == 0 {
        lean_dec_ref(v_as_421_);
        lean_dec_ref(v_inst_420_);
        return v___x_423_;
    } else {
        let mut v___f_427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_428_: u8 = 0;
        v___f_427_ = lean_alloc_closure(
            l_Lake_Toml_encodeArray_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_427_, 0, v_inst_420_);
        v___x_428_ = lean_nat_dec_le(v___x_424_, v___x_424_);
        if v___x_428_ == 0 {
            if v___x_426_ == 0 {
                lean_dec_ref(v___f_427_);
                lean_dec_ref(v_as_421_);
                return v___x_423_;
            } else {
                let mut v___x_429_: usize = 0;
                let mut v___x_430_: usize = 0;
                let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
                v___x_429_ = 0usize;
                v___x_430_ = lean_usize_of_nat(v___x_424_);
                v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
            let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
            v___x_432_ = 0usize;
            v___x_433_ = lean_usize_of_nat(v___x_424_);
            v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_00_u03b1_435_: *mut LeanObject,
    mut v_inst_436_: *mut LeanObject,
    mut v_as_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_436_, v_as_437_);
    return v___x_438_;
}
pub unsafe fn l_Lake_instToToml_x3fArray___redArg___lam__0(
    mut v_inst_439_: *mut LeanObject,
    mut v_as_440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_441_ = l_Lake_Toml_encodeArray_x3f___redArg(v_inst_439_, v_as_440_);
                if lean_obj_tag(v___x_441_) == 0 {
                    v___x_442_ = lean_box(0);
                    return v___x_442_;
                } else {
                    v_val_443_ = lean_ctor_get(v___x_441_, 0);
                    v_isSharedCheck_452_ = (!lean_is_exclusive(v___x_441_)) as u8;
                    if v_isSharedCheck_452_ == 0 {
                        v___x_445_ = v___x_441_;
                        v_isShared_446_ = v_isSharedCheck_452_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_443_);
                        lean_dec(v___x_441_);
                        v___x_445_ = lean_box(0);
                        v_isShared_446_ = v_isSharedCheck_452_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_447_ = lean_box(0);
                v___x_448_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_448_, 0, v___x_447_);
                lean_ctor_set(v___x_448_, 1, v_val_443_);
                if v_isShared_446_ == 0 {
                    lean_ctor_set(v___x_445_, 0, v___x_448_);
                    v___x_450_ = v___x_445_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
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
    mut v_inst_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_454_: *mut LeanObject = core::ptr::null_mut();
    v___f_454_ = lean_alloc_closure(
        l_Lake_instToToml_x3fArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_454_, 0, v_inst_453_);
    return v___f_454_;
}
pub unsafe fn l_Lake_instToToml_x3fArray(
    mut v_00_u03b1_455_: *mut LeanObject,
    mut v_inst_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_457_: *mut LeanObject = core::ptr::null_mut();
    v___f_457_ = lean_alloc_closure(
        l_Lake_instToToml_x3fArray___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_457_, 0, v_inst_456_);
    return v___f_457_;
}
pub unsafe fn l_Lake_instToToml_x3fOption___redArg___lam__0(
    mut v_inst_458_: *mut LeanObject,
    mut v_x_459_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_459_) == 0 {
        let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_458_);
        v___x_460_ = lean_box(0);
        return v___x_460_;
    } else {
        let mut v_val_461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
        v_val_461_ = lean_ctor_get(v_x_459_, 0);
        lean_inc(v_val_461_);
        lean_dec_ref_known(v_x_459_, 1);
        v___x_462_ = lean_apply_1(v_inst_458_, v_val_461_);
        return v___x_462_;
    }
}
pub unsafe fn l_Lake_instToToml_x3fOption___redArg(
    mut v_inst_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_464_: *mut LeanObject = core::ptr::null_mut();
    v___f_464_ = lean_alloc_closure(
        l_Lake_instToToml_x3fOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_464_, 0, v_inst_463_);
    return v___f_464_;
}
pub unsafe fn l_Lake_instToToml_x3fOption(
    mut v_00_u03b1_465_: *mut LeanObject,
    mut v_inst_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_467_: *mut LeanObject = core::ptr::null_mut();
    v___f_467_ = lean_alloc_closure(
        l_Lake_instToToml_x3fOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_467_, 0, v_inst_466_);
    return v___f_467_;
}
pub unsafe fn l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0(
    mut v_inst_468_: *mut LeanObject,
    mut v_x_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_469_) == 0 {
                    lean_dec_ref(v_inst_468_);
                    v___x_470_ = lean_box(0);
                    return v___x_470_;
                } else {
                    v_val_471_ = lean_ctor_get(v_x_469_, 0);
                    v_isSharedCheck_479_ = (!lean_is_exclusive(v_x_469_)) as u8;
                    if v_isSharedCheck_479_ == 0 {
                        v___x_473_ = v_x_469_;
                        v_isShared_474_ = v_isSharedCheck_479_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_471_);
                        lean_dec(v_x_469_);
                        v___x_473_ = lean_box(0);
                        v_isShared_474_ = v_isSharedCheck_479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_475_ = lean_apply_1(v_inst_468_, v_val_471_);
                if v_isShared_474_ == 0 {
                    lean_ctor_set(v___x_473_, 0, v___x_475_);
                    v___x_477_ = v___x_473_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
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
    mut v_inst_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_481_: *mut LeanObject = core::ptr::null_mut();
    v___f_481_ = lean_alloc_closure(
        l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_481_, 0, v_inst_480_);
    return v___f_481_;
}
pub unsafe fn l_Lake_instToToml_x3fOptionOfToToml(
    mut v_00_u03b1_482_: *mut LeanObject,
    mut v_inst_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_484_: *mut LeanObject = core::ptr::null_mut();
    v___f_484_ = lean_alloc_closure(
        l_Lake_instToToml_x3fOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_484_, 0, v_inst_483_);
    return v___f_484_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0(
    mut v_inst_486_: *mut LeanObject,
    mut v_k_487_: *mut LeanObject,
    mut v_v_488_: *mut LeanObject,
    mut v_t_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = lean_apply_1(v_inst_486_, v_v_488_);
    if lean_obj_tag(v___x_490_) == 1 {
        let mut v_val_491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
        v_val_491_ = lean_ctor_get(v___x_490_, 0);
        lean_inc(v_val_491_);
        lean_dec_ref_known(v___x_490_, 1);
        v___x_492_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_493_ = l_Lake_Toml_RBDict_insert___redArg(v___x_492_, v_k_487_, v_val_491_, v_t_489_);
        return v___x_493_;
    } else {
        lean_dec(v___x_490_);
        lean_dec(v_k_487_);
        return v_t_489_;
    }
}
pub unsafe fn l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg(
    mut v_inst_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_495_: *mut LeanObject = core::ptr::null_mut();
    v___f_495_ = lean_alloc_closure(
        l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_495_, 0, v_inst_494_);
    return v___f_495_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertOfToToml_x3f(
    mut v_00_u03b1_496_: *mut LeanObject,
    mut v_inst_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_498_: *mut LeanObject = core::ptr::null_mut();
    v___f_498_ = lean_alloc_closure(
        l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_498_, 0, v_inst_497_);
    return v___f_498_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertTable___lam__0(
    mut v_k_499_: *mut LeanObject,
    mut v_v_500_: *mut LeanObject,
    mut v_t_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    v_items_502_ = lean_ctor_get(v_v_500_, 0);
    v___x_503_ = lean_array_get_size(v_items_502_);
    v___x_504_ = lean_unsigned_to_nat(0);
    v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
    if v___x_505_ == 0 {
        let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
        v___x_506_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_507_ = lean_box(0);
        v___x_508_ = lean_alloc_ctor(6, 2, (0) as u32);
        lean_ctor_set(v___x_508_, 0, v___x_507_);
        lean_ctor_set(v___x_508_, 1, v_v_500_);
        v___x_509_ = l_Lake_Toml_RBDict_insert___redArg(v___x_506_, v_k_499_, v___x_508_, v_t_501_);
        return v___x_509_;
    } else {
        lean_dec_ref(v_v_500_);
        lean_dec(v_k_499_);
        return v_t_501_;
    }
}
pub unsafe fn l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0(
    mut v_inst_512_: *mut LeanObject,
    mut v_k_513_: *mut LeanObject,
    mut v_v_514_: *mut LeanObject,
    mut v_t_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    v___x_516_ = lean_array_get_size(v_v_514_);
    v___x_517_ = lean_unsigned_to_nat(0);
    v___x_518_ = lean_nat_dec_eq(v___x_516_, v___x_517_);
    if v___x_518_ == 0 {
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
        v___x_519_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_520_ = lean_apply_1(v_inst_512_, v_v_514_);
        v___x_521_ = l_Lake_Toml_RBDict_insert___redArg(v___x_519_, v_k_513_, v___x_520_, v_t_515_);
        return v___x_521_;
    } else {
        lean_dec_ref(v_v_514_);
        lean_dec(v_k_513_);
        lean_dec_ref(v_inst_512_);
        return v_t_515_;
    }
}
pub unsafe fn l_Lake_Toml_instSmartInsertArrayOfToToml___redArg(
    mut v_inst_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_523_: *mut LeanObject = core::ptr::null_mut();
    v___f_523_ = lean_alloc_closure(
        l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_523_, 0, v_inst_522_);
    return v___f_523_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertArrayOfToToml(
    mut v_00_u03b1_524_: *mut LeanObject,
    mut v_inst_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_526_: *mut LeanObject = core::ptr::null_mut();
    v___f_526_ = lean_alloc_closure(
        l_Lake_Toml_instSmartInsertArrayOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_526_, 0, v_inst_525_);
    return v___f_526_;
}
pub unsafe fn l_Lake_Toml_instSmartInsertString___lam__0(
    mut v_k_527_: *mut LeanObject,
    mut v_v_528_: *mut LeanObject,
    mut v_t_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    v___x_530_ = lean_string_utf8_byte_size(v_v_528_);
    v___x_531_ = lean_unsigned_to_nat(0);
    v___x_532_ = lean_nat_dec_eq(v___x_530_, v___x_531_);
    if v___x_532_ == 0 {
        let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        v___x_533_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_534_ = lean_box(0);
        v___x_535_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_535_, 0, v___x_534_);
        lean_ctor_set(v___x_535_, 1, v_v_528_);
        v___x_536_ = l_Lake_Toml_RBDict_insert___redArg(v___x_533_, v_k_527_, v___x_535_, v_t_529_);
        return v___x_536_;
    } else {
        lean_dec_ref(v_v_528_);
        lean_dec(v_k_527_);
        return v_t_529_;
    }
}
pub unsafe fn l_Lake_Toml_Table_insert___redArg(
    mut v_enc_539_: *mut LeanObject,
    mut v_k_540_: *mut LeanObject,
    mut v_v_541_: *mut LeanObject,
    mut v_t_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
    v___x_544_ = lean_apply_1(v_enc_539_, v_v_541_);
    v___x_545_ = l_Lake_Toml_RBDict_insert___redArg(v___x_543_, v_k_540_, v___x_544_, v_t_542_);
    return v___x_545_;
}
pub unsafe fn l_Lake_Toml_Table_insert(
    mut v_00_u03b1_546_: *mut LeanObject,
    mut v_enc_547_: *mut LeanObject,
    mut v_k_548_: *mut LeanObject,
    mut v_v_549_: *mut LeanObject,
    mut v_t_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
    v___x_552_ = lean_apply_1(v_enc_547_, v_v_549_);
    v___x_553_ = l_Lake_Toml_RBDict_insert___redArg(v___x_551_, v_k_548_, v___x_552_, v_t_550_);
    return v___x_553_;
}
pub unsafe fn l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0(
    mut v_inst_554_: *mut LeanObject,
    mut v_k_555_: *mut LeanObject,
    mut v_v_x3f_556_: *mut LeanObject,
    mut v_t_557_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_v_x3f_556_) == 0 {
        lean_dec(v_k_555_);
        lean_dec_ref(v_inst_554_);
        return v_t_557_;
    } else {
        let mut v_val_558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
        v_val_558_ = lean_ctor_get(v_v_x3f_556_, 0);
        lean_inc(v_val_558_);
        lean_dec_ref_known(v_v_x3f_556_, 1);
        v___x_559_ = lean_apply_1(v_inst_554_, v_val_558_);
        v___x_560_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_561_ = l_Lake_Toml_RBDict_insert___redArg(v___x_560_, v_k_555_, v___x_559_, v_t_557_);
        return v___x_561_;
    }
}
pub unsafe fn l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg(
    mut v_inst_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_563_: *mut LeanObject = core::ptr::null_mut();
    v___f_563_ = lean_alloc_closure(
        l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_563_, 0, v_inst_562_);
    return v___f_563_;
}
pub unsafe fn l_Lake_Toml_Table_instSmartInsertOptionOfToToml(
    mut v_00_u03b1_564_: *mut LeanObject,
    mut v_inst_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_566_: *mut LeanObject = core::ptr::null_mut();
    v___f_566_ = lean_alloc_closure(
        l_Lake_Toml_Table_instSmartInsertOptionOfToToml___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_566_, 0, v_inst_565_);
    return v___f_566_;
}
pub unsafe fn l_Lake_Toml_Table_smartInsert___redArg(
    mut v_inst_567_: *mut LeanObject,
    mut v_k_568_: *mut LeanObject,
    mut v_v_569_: *mut LeanObject,
    mut v_t_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = lean_apply_3(v_inst_567_, v_k_568_, v_v_569_, v_t_570_);
    return v___x_571_;
}
pub unsafe fn l_Lake_Toml_Table_smartInsert(
    mut v_00_u03b1_572_: *mut LeanObject,
    mut v_inst_573_: *mut LeanObject,
    mut v_k_574_: *mut LeanObject,
    mut v_v_575_: *mut LeanObject,
    mut v_t_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    v___x_577_ = lean_apply_3(v_inst_573_, v_k_574_, v_v_575_, v_t_576_);
    return v___x_577_;
}
pub unsafe fn l_Lake_Toml_Table_insertD___redArg(
    mut v_enc_578_: *mut LeanObject,
    mut v_inst_579_: *mut LeanObject,
    mut v_k_580_: *mut LeanObject,
    mut v_v_581_: *mut LeanObject,
    mut v_default_582_: *mut LeanObject,
    mut v_t_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: u8 = 0;
    lean_inc(v_v_581_);
    v___x_584_ = lean_apply_2(v_inst_579_, v_v_581_, v_default_582_);
    v___x_585_ = (lean_unbox(v___x_584_) as u8);
    if v___x_585_ == 0 {
        let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
        v___x_586_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_587_ = lean_apply_1(v_enc_578_, v_v_581_);
        v___x_588_ = l_Lake_Toml_RBDict_insert___redArg(v___x_586_, v_k_580_, v___x_587_, v_t_583_);
        return v___x_588_;
    } else {
        lean_dec(v_v_581_);
        lean_dec(v_k_580_);
        lean_dec_ref(v_enc_578_);
        return v_t_583_;
    }
}
pub unsafe fn l_Lake_Toml_Table_insertD(
    mut v_00_u03b1_589_: *mut LeanObject,
    mut v_enc_590_: *mut LeanObject,
    mut v_inst_591_: *mut LeanObject,
    mut v_k_592_: *mut LeanObject,
    mut v_v_593_: *mut LeanObject,
    mut v_default_594_: *mut LeanObject,
    mut v_t_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    lean_inc(v_v_593_);
    v___x_596_ = lean_apply_2(v_inst_591_, v_v_593_, v_default_594_);
    v___x_597_ = (lean_unbox(v___x_596_) as u8);
    if v___x_597_ == 0 {
        let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
        v___x_598_ = l_Lake_Toml_instSmartInsertOfToToml_x3f___redArg___lam__0___closed__0;
        v___x_599_ = lean_apply_1(v_enc_590_, v_v_593_);
        v___x_600_ = l_Lake_Toml_RBDict_insert___redArg(v___x_598_, v_k_592_, v___x_599_, v_t_595_);
        return v___x_600_;
    } else {
        lean_dec(v_v_593_);
        lean_dec(v_k_592_);
        lean_dec_ref(v_enc_590_);
        return v_t_595_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Encode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Encode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Encode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Toml_Data_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Encode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Encode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Encode(builtin);
}
