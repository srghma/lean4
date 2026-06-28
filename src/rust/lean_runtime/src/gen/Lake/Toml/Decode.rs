// Lean compiler output
// Module: Lake.Toml.Decode
// Imports: Init.System.FilePath Lake.Toml.Data Init.Data.ToString.Macro
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_mapFinIdxM_map___redArg,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Meta::Defs::l_String_toName;
use crate::r#gen::Init::Prelude::{l_Array_push___boxed, l_EStateM_pure};
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, runtime_initialize_Init_System_FilePath,
};
use crate::r#gen::Lake::Toml::Data::Dict::l_Lake_Toml_RBDict_findEntry_x3f___redArg;
use crate::r#gen::Lake::Toml::Data::Value::l_Lake_Toml_ppKey;
use crate::r#gen::Lake::Toml::Data::{
    initialize_Lake_Toml_Data, runtime_initialize_Lake_Toml_Data,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_box_float, lean_closure_set, lean_ctor_get, lean_ctor_get_float,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_Toml_decodeArray___redArg___lam__0___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_push___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lake_Toml_decodeArray___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__3_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__4_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__5_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__6_value: LeanClosureObject<0> =
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
static mut l_Lake_Toml_decodeArray___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_decodeArray___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_decodeArray___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lake_Toml_decodeArray___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_decodeArray___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeArray___redArg___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0_value:
    LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_EStateM_pure as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Decode_0__Lake_Toml_instDecodeTomlValue___closed__0_value
)
    as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeString___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeString as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlString___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlString___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlFilePath___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeName___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeName___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlName___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeName as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlName___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlName: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlName___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeInt___closed__0_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 110, 116, 101, 103, 101, 114, 0,
    ],
};
static mut l_Lake_Toml_Value_decodeInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeInt___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlInt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeInt as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlInt___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeNat___closed__0_value: LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 111, 110, 110, 101, 103, 97, 116, 105, 118,
        101, 32, 105, 110, 116, 101, 103, 101, 114, 0,
    ],
};
static mut l_Lake_Toml_Value_decodeNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeNat___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_Value_decodeNat___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_Value_decodeNat___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_Value_instDecodeTomlNat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeNat as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlNat___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeFloat___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 108, 111, 97, 116, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeFloat___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlFloat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeFloat as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlFloat___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlFloat: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlFloat___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeBool___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 98, 111, 111, 108, 101, 97, 110, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeBool___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlBool___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeBool as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlBool___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlBool___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeDateTime___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 97, 116, 101, 45, 116, 105, 109, 101, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeDateTime___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_decodeDateTime as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_Toml_Value_instDecodeTomlDateTime: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_instDecodeTomlDateTime___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeValueArray___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 114, 114, 97, 121, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeValueArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeValueArray___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_decodeTable___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 97, 98, 108, 101, 0,
        ],
    };
static mut l_Lake_Toml_Value_decodeTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_decodeTable___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0_value:
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
    m_fun: l_Lake_Toml_Value_decodeTable as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Decode_0__Lake_Toml_Value_instDecodeTomlTable___closed__0_value
) as *mut LeanObject;
pub static l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0_value: LeanStringObject<5> =
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
        m_data: [107, 101, 121, 32, 0],
    };
static mut l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1_value: LeanStringObject<3> =
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
        m_data: [58, 32, 0],
    };
static mut l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_Toml_Table_decodeValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Table_decodeValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Table_decodeValue___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Table_decodeValue___closed__1_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            109, 105, 115, 115, 105, 110, 103, 32, 114, 101, 113, 117, 105, 114, 101, 100, 32, 107,
            101, 121, 58, 32, 0,
        ],
    };
static mut l_Lake_Toml_Table_decodeValue___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Table_decodeValue___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_Table_decodeNameMap___redArg___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_pure as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_Toml_Table_decodeNameMap___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Table_decodeNameMap___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_decodeToml___redArg(
    mut v_inst_1281_: *mut LeanObject,
    mut v_v_1282_: *mut LeanObject,
    mut v_a_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = lean_apply_2(v_inst_1281_, v_v_1282_, v_a_1283_);
    return v___x_1284_;
}
pub unsafe fn l_Lake_decodeToml(
    mut v_00_u03b1_1285_: *mut LeanObject,
    mut v_inst_1286_: *mut LeanObject,
    mut v_v_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1289_ = lean_apply_2(v_inst_1286_, v_v_1287_, v_a_1288_);
    return v___x_1289_;
}
pub unsafe fn l_Lake_Toml_ensureDecode___redArg(
    mut v_x_1290_: *mut LeanObject,
    mut v_es_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: u8 = 0;
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1292_ = lean_apply_1(v_x_1290_, v_es_1291_);
                v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
                v_a_1294_ = lean_ctor_get(v___x_1292_, 1);
                v_isSharedCheck_1308_ = (!lean_is_exclusive(v___x_1292_)) as u8;
                if v_isSharedCheck_1308_ == 0 {
                    v___x_1296_ = v___x_1292_;
                    v_isShared_1297_ = v_isSharedCheck_1308_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1294_);
                    lean_inc(v_a_1293_);
                    lean_dec(v___x_1292_);
                    v___x_1296_ = lean_box(0);
                    v_isShared_1297_ = v_isSharedCheck_1308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1298_ = lean_array_get_size(v_a_1294_);
                v___x_1299_ = lean_unsigned_to_nat(0);
                v___x_1300_ = lean_nat_dec_eq(v___x_1298_, v___x_1299_);
                if v___x_1300_ == 0 {
                    lean_dec(v_a_1293_);
                    v___x_1301_ = lean_box(0);
                    if v_isShared_1297_ == 0 {
                        lean_ctor_set_tag(v___x_1296_, 1);
                        lean_ctor_set(v___x_1296_, 0, v___x_1301_);
                        v___x_1303_ = v___x_1296_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
                        lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1294_);
                        v___x_1303_ = v_reuseFailAlloc_1304_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1297_ == 0 {
                        v___x_1306_ = v___x_1296_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1293_);
                        lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_a_1294_);
                        v___x_1306_ = v_reuseFailAlloc_1307_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1303_;
            }
            3 => {
                return v___x_1306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_ensureDecode(
    mut v_00_u03b1_1309_: *mut LeanObject,
    mut v_x_1310_: *mut LeanObject,
    mut v_es_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1317_: u8 = 0;
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = lean_apply_1(v_x_1310_, v_es_1311_);
                v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
                v_a_1314_ = lean_ctor_get(v___x_1312_, 1);
                v_isSharedCheck_1328_ = (!lean_is_exclusive(v___x_1312_)) as u8;
                if v_isSharedCheck_1328_ == 0 {
                    v___x_1316_ = v___x_1312_;
                    v_isShared_1317_ = v_isSharedCheck_1328_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1314_);
                    lean_inc(v_a_1313_);
                    lean_dec(v___x_1312_);
                    v___x_1316_ = lean_box(0);
                    v_isShared_1317_ = v_isSharedCheck_1328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1318_ = lean_array_get_size(v_a_1314_);
                v___x_1319_ = lean_unsigned_to_nat(0);
                v___x_1320_ = lean_nat_dec_eq(v___x_1318_, v___x_1319_);
                if v___x_1320_ == 0 {
                    lean_dec(v_a_1313_);
                    v___x_1321_ = lean_box(0);
                    if v_isShared_1317_ == 0 {
                        lean_ctor_set_tag(v___x_1316_, 1);
                        lean_ctor_set(v___x_1316_, 0, v___x_1321_);
                        v___x_1323_ = v___x_1316_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
                        lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_a_1314_);
                        v___x_1323_ = v_reuseFailAlloc_1324_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1317_ == 0 {
                        v___x_1326_ = v___x_1316_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1313_);
                        lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1314_);
                        v___x_1326_ = v_reuseFailAlloc_1327_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1323_;
            }
            3 => {
                return v___x_1326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_tryDecodeD___redArg(
    mut v_default_1329_: *mut LeanObject,
    mut v_x_1330_: *mut LeanObject,
    mut v_es_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut v_a_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_unused_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1332_ = lean_apply_1(v_x_1330_, v_es_1331_);
                if lean_obj_tag(v___x_1332_) == 0 {
                    lean_dec(v_default_1329_);
                    v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
                    v_a_1334_ = lean_ctor_get(v___x_1332_, 1);
                    v_isSharedCheck_1341_ = (!lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1336_ = v___x_1332_;
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1334_);
                        lean_inc(v_a_1333_);
                        lean_dec(v___x_1332_);
                        v___x_1336_ = lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1342_ = lean_ctor_get(v___x_1332_, 1);
                    v_isSharedCheck_1349_ = (!lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1349_ == 0 {
                        v_unused_1350_ = lean_ctor_get(v___x_1332_, 0);
                        lean_dec(v_unused_1350_);
                        v___x_1344_ = v___x_1332_;
                        v_isShared_1345_ = v_isSharedCheck_1349_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1342_);
                        lean_dec(v___x_1332_);
                        v___x_1344_ = lean_box(0);
                        v_isShared_1345_ = v_isSharedCheck_1349_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1337_ == 0 {
                    v___x_1339_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1333_);
                    lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_a_1334_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1339_;
            }
            3 => {
                if v_isShared_1345_ == 0 {
                    lean_ctor_set_tag(v___x_1344_, 0);
                    lean_ctor_set(v___x_1344_, 0, v_default_1329_);
                    v___x_1347_ = v___x_1344_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_default_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_a_1342_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_tryDecodeD(
    mut v_00_u03b1_1351_: *mut LeanObject,
    mut v_default_1352_: *mut LeanObject,
    mut v_x_1353_: *mut LeanObject,
    mut v_es_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1360_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut v_a_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_unused_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1355_ = lean_apply_1(v_x_1353_, v_es_1354_);
                if lean_obj_tag(v___x_1355_) == 0 {
                    lean_dec(v_default_1352_);
                    v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
                    v_a_1357_ = lean_ctor_get(v___x_1355_, 1);
                    v_isSharedCheck_1364_ = (!lean_is_exclusive(v___x_1355_)) as u8;
                    if v_isSharedCheck_1364_ == 0 {
                        v___x_1359_ = v___x_1355_;
                        v_isShared_1360_ = v_isSharedCheck_1364_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1357_);
                        lean_inc(v_a_1356_);
                        lean_dec(v___x_1355_);
                        v___x_1359_ = lean_box(0);
                        v_isShared_1360_ = v_isSharedCheck_1364_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1365_ = lean_ctor_get(v___x_1355_, 1);
                    v_isSharedCheck_1372_ = (!lean_is_exclusive(v___x_1355_)) as u8;
                    if v_isSharedCheck_1372_ == 0 {
                        v_unused_1373_ = lean_ctor_get(v___x_1355_, 0);
                        lean_dec(v_unused_1373_);
                        v___x_1367_ = v___x_1355_;
                        v_isShared_1368_ = v_isSharedCheck_1372_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1365_);
                        lean_dec(v___x_1355_);
                        v___x_1367_ = lean_box(0);
                        v_isShared_1368_ = v_isSharedCheck_1372_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1360_ == 0 {
                    v___x_1362_ = v___x_1359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1356_);
                    lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1357_);
                    v___x_1362_ = v_reuseFailAlloc_1363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1362_;
            }
            3 => {
                if v_isShared_1368_ == 0 {
                    lean_ctor_set_tag(v___x_1367_, 0);
                    lean_ctor_set(v___x_1367_, 0, v_default_1352_);
                    v___x_1370_ = v___x_1367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_default_1352_);
                    lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1365_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_tryDecode_x3f___redArg(
    mut v_x_1374_: *mut LeanObject,
    mut v_es_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1386_: u8 = 0;
    let mut v_a_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_unused_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1376_ = lean_apply_1(v_x_1374_, v_es_1375_);
                if lean_obj_tag(v___x_1376_) == 0 {
                    v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
                    v_a_1378_ = lean_ctor_get(v___x_1376_, 1);
                    v_isSharedCheck_1386_ = (!lean_is_exclusive(v___x_1376_)) as u8;
                    if v_isSharedCheck_1386_ == 0 {
                        v___x_1380_ = v___x_1376_;
                        v_isShared_1381_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1378_);
                        lean_inc(v_a_1377_);
                        lean_dec(v___x_1376_);
                        v___x_1380_ = lean_box(0);
                        v_isShared_1381_ = v_isSharedCheck_1386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1387_ = lean_ctor_get(v___x_1376_, 1);
                    v_isSharedCheck_1395_ = (!lean_is_exclusive(v___x_1376_)) as u8;
                    if v_isSharedCheck_1395_ == 0 {
                        v_unused_1396_ = lean_ctor_get(v___x_1376_, 0);
                        lean_dec(v_unused_1396_);
                        v___x_1389_ = v___x_1376_;
                        v_isShared_1390_ = v_isSharedCheck_1395_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1387_);
                        lean_dec(v___x_1376_);
                        v___x_1389_ = lean_box(0);
                        v_isShared_1390_ = v_isSharedCheck_1395_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1382_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1382_, 0, v_a_1377_);
                if v_isShared_1381_ == 0 {
                    lean_ctor_set(v___x_1380_, 0, v___x_1382_);
                    v___x_1384_ = v___x_1380_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
                    lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_a_1378_);
                    v___x_1384_ = v_reuseFailAlloc_1385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1384_;
            }
            3 => {
                v___x_1391_ = lean_box(0);
                if v_isShared_1390_ == 0 {
                    lean_ctor_set_tag(v___x_1389_, 0);
                    lean_ctor_set(v___x_1389_, 0, v___x_1391_);
                    v___x_1393_ = v___x_1389_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_a_1387_);
                    v___x_1393_ = v_reuseFailAlloc_1394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_tryDecode_x3f(
    mut v_00_u03b1_1397_: *mut LeanObject,
    mut v_x_1398_: *mut LeanObject,
    mut v_es_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1405_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_a_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1414_: u8 = 0;
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_unused_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = lean_apply_1(v_x_1398_, v_es_1399_);
                if lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
                    v_a_1402_ = lean_ctor_get(v___x_1400_, 1);
                    v_isSharedCheck_1410_ = (!lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1410_ == 0 {
                        v___x_1404_ = v___x_1400_;
                        v_isShared_1405_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1402_);
                        lean_inc(v_a_1401_);
                        lean_dec(v___x_1400_);
                        v___x_1404_ = lean_box(0);
                        v_isShared_1405_ = v_isSharedCheck_1410_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1411_ = lean_ctor_get(v___x_1400_, 1);
                    v_isSharedCheck_1419_ = (!lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1419_ == 0 {
                        v_unused_1420_ = lean_ctor_get(v___x_1400_, 0);
                        lean_dec(v_unused_1420_);
                        v___x_1413_ = v___x_1400_;
                        v_isShared_1414_ = v_isSharedCheck_1419_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1411_);
                        lean_dec(v___x_1400_);
                        v___x_1413_ = lean_box(0);
                        v_isShared_1414_ = v_isSharedCheck_1419_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1406_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1406_, 0, v_a_1401_);
                if v_isShared_1405_ == 0 {
                    lean_ctor_set(v___x_1404_, 0, v___x_1406_);
                    v___x_1408_ = v___x_1404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1402_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1408_;
            }
            3 => {
                v___x_1415_ = lean_box(0);
                if v_isShared_1414_ == 0 {
                    lean_ctor_set_tag(v___x_1413_, 0);
                    lean_ctor_set(v___x_1413_, 0, v___x_1415_);
                    v___x_1417_ = v___x_1413_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
                    lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_a_1411_);
                    v___x_1417_ = v_reuseFailAlloc_1418_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_tryDecode___redArg(
    mut v_inst_1421_: *mut LeanObject,
    mut v_x_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1429_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut v_a_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1441_: u8 = 0;
    let mut v_unused_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1424_ = lean_apply_1(v_x_1422_, v_a_1423_);
                if lean_obj_tag(v___x_1424_) == 0 {
                    lean_dec(v_inst_1421_);
                    v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
                    v_a_1426_ = lean_ctor_get(v___x_1424_, 1);
                    v_isSharedCheck_1433_ = (!lean_is_exclusive(v___x_1424_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1428_ = v___x_1424_;
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1426_);
                        lean_inc(v_a_1425_);
                        lean_dec(v___x_1424_);
                        v___x_1428_ = lean_box(0);
                        v_isShared_1429_ = v_isSharedCheck_1433_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1434_ = lean_ctor_get(v___x_1424_, 1);
                    v_isSharedCheck_1441_ = (!lean_is_exclusive(v___x_1424_)) as u8;
                    if v_isSharedCheck_1441_ == 0 {
                        v_unused_1442_ = lean_ctor_get(v___x_1424_, 0);
                        lean_dec(v_unused_1442_);
                        v___x_1436_ = v___x_1424_;
                        v_isShared_1437_ = v_isSharedCheck_1441_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1434_);
                        lean_dec(v___x_1424_);
                        v___x_1436_ = lean_box(0);
                        v_isShared_1437_ = v_isSharedCheck_1441_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1429_ == 0 {
                    v___x_1431_ = v___x_1428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1425_);
                    lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_a_1426_);
                    v___x_1431_ = v_reuseFailAlloc_1432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1431_;
            }
            3 => {
                if v_isShared_1437_ == 0 {
                    lean_ctor_set_tag(v___x_1436_, 0);
                    lean_ctor_set(v___x_1436_, 0, v_inst_1421_);
                    v___x_1439_ = v___x_1436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_inst_1421_);
                    lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_a_1434_);
                    v___x_1439_ = v_reuseFailAlloc_1440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_tryDecode(
    mut v_00_u03b1_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_x_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v_a_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1460_: u8 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1464_: u8 = 0;
    let mut v_unused_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1447_ = lean_apply_1(v_x_1445_, v_a_1446_);
                if lean_obj_tag(v___x_1447_) == 0 {
                    lean_dec(v_inst_1444_);
                    v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
                    v_a_1449_ = lean_ctor_get(v___x_1447_, 1);
                    v_isSharedCheck_1456_ = (!lean_is_exclusive(v___x_1447_)) as u8;
                    if v_isSharedCheck_1456_ == 0 {
                        v___x_1451_ = v___x_1447_;
                        v_isShared_1452_ = v_isSharedCheck_1456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1449_);
                        lean_inc(v_a_1448_);
                        lean_dec(v___x_1447_);
                        v___x_1451_ = lean_box(0);
                        v_isShared_1452_ = v_isSharedCheck_1456_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1457_ = lean_ctor_get(v___x_1447_, 1);
                    v_isSharedCheck_1464_ = (!lean_is_exclusive(v___x_1447_)) as u8;
                    if v_isSharedCheck_1464_ == 0 {
                        v_unused_1465_ = lean_ctor_get(v___x_1447_, 0);
                        lean_dec(v_unused_1465_);
                        v___x_1459_ = v___x_1447_;
                        v_isShared_1460_ = v_isSharedCheck_1464_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1457_);
                        lean_dec(v___x_1447_);
                        v___x_1459_ = lean_box(0);
                        v_isShared_1460_ = v_isSharedCheck_1464_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1452_ == 0 {
                    v___x_1454_ = v___x_1451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1448_);
                    lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_a_1449_);
                    v___x_1454_ = v_reuseFailAlloc_1455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1454_;
            }
            3 => {
                if v_isShared_1460_ == 0 {
                    lean_ctor_set_tag(v___x_1459_, 0);
                    lean_ctor_set(v___x_1459_, 0, v_inst_1444_);
                    v___x_1462_ = v___x_1459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_inst_1444_);
                    lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_a_1457_);
                    v___x_1462_ = v_reuseFailAlloc_1463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_optDecodeD___redArg(
    mut v_default_1466_: *mut LeanObject,
    mut v_a_x3f_1467_: *mut LeanObject,
    mut v_f_1468_: *mut LeanObject,
    mut v_a_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1481_: u8 = 0;
    let mut v_a_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_unused_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_x3f_1467_) == 0 {
                    lean_dec_ref(v_f_1468_);
                    v___x_1470_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1470_, 0, v_default_1466_);
                    lean_ctor_set(v___x_1470_, 1, v_a_1469_);
                    return v___x_1470_;
                } else {
                    v_val_1471_ = lean_ctor_get(v_a_x3f_1467_, 0);
                    lean_inc(v_val_1471_);
                    lean_dec_ref_known(v_a_x3f_1467_, 1);
                    v___x_1472_ = lean_apply_2(v_f_1468_, v_val_1471_, v_a_1469_);
                    if lean_obj_tag(v___x_1472_) == 0 {
                        lean_dec(v_default_1466_);
                        v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
                        v_a_1474_ = lean_ctor_get(v___x_1472_, 1);
                        v_isSharedCheck_1481_ = (!lean_is_exclusive(v___x_1472_)) as u8;
                        if v_isSharedCheck_1481_ == 0 {
                            v___x_1476_ = v___x_1472_;
                            v_isShared_1477_ = v_isSharedCheck_1481_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1474_);
                            lean_inc(v_a_1473_);
                            lean_dec(v___x_1472_);
                            v___x_1476_ = lean_box(0);
                            v_isShared_1477_ = v_isSharedCheck_1481_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1482_ = lean_ctor_get(v___x_1472_, 1);
                        v_isSharedCheck_1489_ = (!lean_is_exclusive(v___x_1472_)) as u8;
                        if v_isSharedCheck_1489_ == 0 {
                            v_unused_1490_ = lean_ctor_get(v___x_1472_, 0);
                            lean_dec(v_unused_1490_);
                            v___x_1484_ = v___x_1472_;
                            v_isShared_1485_ = v_isSharedCheck_1489_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1482_);
                            lean_dec(v___x_1472_);
                            v___x_1484_ = lean_box(0);
                            v_isShared_1485_ = v_isSharedCheck_1489_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1477_ == 0 {
                    v___x_1479_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1473_);
                    lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_a_1474_);
                    v___x_1479_ = v_reuseFailAlloc_1480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1479_;
            }
            3 => {
                if v_isShared_1485_ == 0 {
                    lean_ctor_set_tag(v___x_1484_, 0);
                    lean_ctor_set(v___x_1484_, 0, v_default_1466_);
                    v___x_1487_ = v___x_1484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_default_1466_);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_a_1482_);
                    v___x_1487_ = v_reuseFailAlloc_1488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_optDecodeD(
    mut v_00_u03b2_1491_: *mut LeanObject,
    mut v_00_u03b1_1492_: *mut LeanObject,
    mut v_default_1493_: *mut LeanObject,
    mut v_a_x3f_1494_: *mut LeanObject,
    mut v_f_1495_: *mut LeanObject,
    mut v_a_1496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_a_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_unused_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_x3f_1494_) == 0 {
                    lean_dec_ref(v_f_1495_);
                    v___x_1497_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1497_, 0, v_default_1493_);
                    lean_ctor_set(v___x_1497_, 1, v_a_1496_);
                    return v___x_1497_;
                } else {
                    v_val_1498_ = lean_ctor_get(v_a_x3f_1494_, 0);
                    lean_inc(v_val_1498_);
                    lean_dec_ref_known(v_a_x3f_1494_, 1);
                    v___x_1499_ = lean_apply_2(v_f_1495_, v_val_1498_, v_a_1496_);
                    if lean_obj_tag(v___x_1499_) == 0 {
                        lean_dec(v_default_1493_);
                        v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
                        v_a_1501_ = lean_ctor_get(v___x_1499_, 1);
                        v_isSharedCheck_1508_ = (!lean_is_exclusive(v___x_1499_)) as u8;
                        if v_isSharedCheck_1508_ == 0 {
                            v___x_1503_ = v___x_1499_;
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1501_);
                            lean_inc(v_a_1500_);
                            lean_dec(v___x_1499_);
                            v___x_1503_ = lean_box(0);
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1509_ = lean_ctor_get(v___x_1499_, 1);
                        v_isSharedCheck_1516_ = (!lean_is_exclusive(v___x_1499_)) as u8;
                        if v_isSharedCheck_1516_ == 0 {
                            v_unused_1517_ = lean_ctor_get(v___x_1499_, 0);
                            lean_dec(v_unused_1517_);
                            v___x_1511_ = v___x_1499_;
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1509_);
                            lean_dec(v___x_1499_);
                            v___x_1511_ = lean_box(0);
                            v_isShared_1512_ = v_isSharedCheck_1516_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1504_ == 0 {
                    v___x_1506_ = v___x_1503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1500_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_a_1501_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1506_;
            }
            3 => {
                if v_isShared_1512_ == 0 {
                    lean_ctor_set_tag(v___x_1511_, 0);
                    lean_ctor_set(v___x_1511_, 0, v_default_1493_);
                    v___x_1514_ = v___x_1511_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_default_1493_);
                    lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_a_1509_);
                    v___x_1514_ = v_reuseFailAlloc_1515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_optDecode___redArg(
    mut v_inst_1518_: *mut LeanObject,
    mut v_a_x3f_1519_: *mut LeanObject,
    mut v_f_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_a_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1537_: u8 = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_unused_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_x3f_1519_) == 0 {
                    lean_dec_ref(v_f_1520_);
                    v___x_1522_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1522_, 0, v_inst_1518_);
                    lean_ctor_set(v___x_1522_, 1, v_a_1521_);
                    return v___x_1522_;
                } else {
                    v_val_1523_ = lean_ctor_get(v_a_x3f_1519_, 0);
                    lean_inc(v_val_1523_);
                    lean_dec_ref_known(v_a_x3f_1519_, 1);
                    v___x_1524_ = lean_apply_2(v_f_1520_, v_val_1523_, v_a_1521_);
                    if lean_obj_tag(v___x_1524_) == 0 {
                        lean_dec(v_inst_1518_);
                        v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
                        v_a_1526_ = lean_ctor_get(v___x_1524_, 1);
                        v_isSharedCheck_1533_ = (!lean_is_exclusive(v___x_1524_)) as u8;
                        if v_isSharedCheck_1533_ == 0 {
                            v___x_1528_ = v___x_1524_;
                            v_isShared_1529_ = v_isSharedCheck_1533_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1526_);
                            lean_inc(v_a_1525_);
                            lean_dec(v___x_1524_);
                            v___x_1528_ = lean_box(0);
                            v_isShared_1529_ = v_isSharedCheck_1533_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1534_ = lean_ctor_get(v___x_1524_, 1);
                        v_isSharedCheck_1541_ = (!lean_is_exclusive(v___x_1524_)) as u8;
                        if v_isSharedCheck_1541_ == 0 {
                            v_unused_1542_ = lean_ctor_get(v___x_1524_, 0);
                            lean_dec(v_unused_1542_);
                            v___x_1536_ = v___x_1524_;
                            v_isShared_1537_ = v_isSharedCheck_1541_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1534_);
                            lean_dec(v___x_1524_);
                            v___x_1536_ = lean_box(0);
                            v_isShared_1537_ = v_isSharedCheck_1541_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1529_ == 0 {
                    v___x_1531_ = v___x_1528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1525_);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_a_1526_);
                    v___x_1531_ = v_reuseFailAlloc_1532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1531_;
            }
            3 => {
                if v_isShared_1537_ == 0 {
                    lean_ctor_set_tag(v___x_1536_, 0);
                    lean_ctor_set(v___x_1536_, 0, v_inst_1518_);
                    v___x_1539_ = v___x_1536_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_inst_1518_);
                    lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_a_1534_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_optDecode(
    mut v_00_u03b2_1543_: *mut LeanObject,
    mut v_00_u03b1_1544_: *mut LeanObject,
    mut v_inst_1545_: *mut LeanObject,
    mut v_a_x3f_1546_: *mut LeanObject,
    mut v_f_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_a_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_unused_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_x3f_1546_) == 0 {
                    lean_dec_ref(v_f_1547_);
                    v___x_1549_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1549_, 0, v_inst_1545_);
                    lean_ctor_set(v___x_1549_, 1, v_a_1548_);
                    return v___x_1549_;
                } else {
                    v_val_1550_ = lean_ctor_get(v_a_x3f_1546_, 0);
                    lean_inc(v_val_1550_);
                    lean_dec_ref_known(v_a_x3f_1546_, 1);
                    v___x_1551_ = lean_apply_2(v_f_1547_, v_val_1550_, v_a_1548_);
                    if lean_obj_tag(v___x_1551_) == 0 {
                        lean_dec(v_inst_1545_);
                        v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
                        v_a_1553_ = lean_ctor_get(v___x_1551_, 1);
                        v_isSharedCheck_1560_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                        if v_isSharedCheck_1560_ == 0 {
                            v___x_1555_ = v___x_1551_;
                            v_isShared_1556_ = v_isSharedCheck_1560_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1553_);
                            lean_inc(v_a_1552_);
                            lean_dec(v___x_1551_);
                            v___x_1555_ = lean_box(0);
                            v_isShared_1556_ = v_isSharedCheck_1560_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1561_ = lean_ctor_get(v___x_1551_, 1);
                        v_isSharedCheck_1568_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                        if v_isSharedCheck_1568_ == 0 {
                            v_unused_1569_ = lean_ctor_get(v___x_1551_, 0);
                            lean_dec(v_unused_1569_);
                            v___x_1563_ = v___x_1551_;
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1561_);
                            lean_dec(v___x_1551_);
                            v___x_1563_ = lean_box(0);
                            v_isShared_1564_ = v_isSharedCheck_1568_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1556_ == 0 {
                    v___x_1558_ = v___x_1555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1552_);
                    lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1553_);
                    v___x_1558_ = v_reuseFailAlloc_1559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1558_;
            }
            3 => {
                if v_isShared_1564_ == 0 {
                    lean_ctor_set_tag(v___x_1563_, 0);
                    lean_ctor_set(v___x_1563_, 0, v_inst_1545_);
                    v___x_1566_ = v___x_1563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_inst_1545_);
                    lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_a_1561_);
                    v___x_1566_ = v_reuseFailAlloc_1567_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_optDecode_x3f___redArg(
    mut v_a_x3f_1570_: *mut LeanObject,
    mut v_f_1571_: *mut LeanObject,
    mut v_a_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_a_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1595_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v_unused_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1573_ = lean_box(0);
                if lean_obj_tag(v_a_x3f_1570_) == 0 {
                    lean_dec_ref(v_f_1571_);
                    v___x_1574_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1574_, 0, v___x_1573_);
                    lean_ctor_set(v___x_1574_, 1, v_a_1572_);
                    return v___x_1574_;
                } else {
                    v_val_1575_ = lean_ctor_get(v_a_x3f_1570_, 0);
                    v_isSharedCheck_1601_ = (!lean_is_exclusive(v_a_x3f_1570_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v___x_1577_ = v_a_x3f_1570_;
                        v_isShared_1578_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1575_);
                        lean_dec(v_a_x3f_1570_);
                        v___x_1577_ = lean_box(0);
                        v_isShared_1578_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1579_ = lean_apply_2(v_f_1571_, v_val_1575_, v_a_1572_);
                if lean_obj_tag(v___x_1579_) == 0 {
                    v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
                    v_a_1581_ = lean_ctor_get(v___x_1579_, 1);
                    v_isSharedCheck_1591_ = (!lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1591_ == 0 {
                        v___x_1583_ = v___x_1579_;
                        v_isShared_1584_ = v_isSharedCheck_1591_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1581_);
                        lean_inc(v_a_1580_);
                        lean_dec(v___x_1579_);
                        v___x_1583_ = lean_box(0);
                        v_isShared_1584_ = v_isSharedCheck_1591_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1577_);
                    v_a_1592_ = lean_ctor_get(v___x_1579_, 1);
                    v_isSharedCheck_1599_ = (!lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1599_ == 0 {
                        v_unused_1600_ = lean_ctor_get(v___x_1579_, 0);
                        lean_dec(v_unused_1600_);
                        v___x_1594_ = v___x_1579_;
                        v_isShared_1595_ = v_isSharedCheck_1599_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1592_);
                        lean_dec(v___x_1579_);
                        v___x_1594_ = lean_box(0);
                        v_isShared_1595_ = v_isSharedCheck_1599_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1578_ == 0 {
                    lean_ctor_set(v___x_1577_, 0, v_a_1580_);
                    v___x_1586_ = v___x_1577_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1580_);
                    v___x_1586_ = v_reuseFailAlloc_1590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1584_ == 0 {
                    lean_ctor_set(v___x_1583_, 0, v___x_1586_);
                    v___x_1588_ = v___x_1583_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_a_1581_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1588_;
            }
            5 => {
                if v_isShared_1595_ == 0 {
                    lean_ctor_set_tag(v___x_1594_, 0);
                    lean_ctor_set(v___x_1594_, 0, v___x_1573_);
                    v___x_1597_ = v___x_1594_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1573_);
                    lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1592_);
                    v___x_1597_ = v_reuseFailAlloc_1598_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_optDecode_x3f(
    mut v_00_u03b1_1602_: *mut LeanObject,
    mut v_00_u03b2_1603_: *mut LeanObject,
    mut v_a_x3f_1604_: *mut LeanObject,
    mut v_f_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_unused_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1607_ = lean_box(0);
                if lean_obj_tag(v_a_x3f_1604_) == 0 {
                    lean_dec_ref(v_f_1605_);
                    v___x_1608_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1608_, 0, v___x_1607_);
                    lean_ctor_set(v___x_1608_, 1, v_a_1606_);
                    return v___x_1608_;
                } else {
                    v_val_1609_ = lean_ctor_get(v_a_x3f_1604_, 0);
                    v_isSharedCheck_1635_ = (!lean_is_exclusive(v_a_x3f_1604_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1611_ = v_a_x3f_1604_;
                        v_isShared_1612_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1609_);
                        lean_dec(v_a_x3f_1604_);
                        v___x_1611_ = lean_box(0);
                        v_isShared_1612_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1613_ = lean_apply_2(v_f_1605_, v_val_1609_, v_a_1606_);
                if lean_obj_tag(v___x_1613_) == 0 {
                    v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
                    v_a_1615_ = lean_ctor_get(v___x_1613_, 1);
                    v_isSharedCheck_1625_ = (!lean_is_exclusive(v___x_1613_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1617_ = v___x_1613_;
                        v_isShared_1618_ = v_isSharedCheck_1625_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1615_);
                        lean_inc(v_a_1614_);
                        lean_dec(v___x_1613_);
                        v___x_1617_ = lean_box(0);
                        v_isShared_1618_ = v_isSharedCheck_1625_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1611_);
                    v_a_1626_ = lean_ctor_get(v___x_1613_, 1);
                    v_isSharedCheck_1633_ = (!lean_is_exclusive(v___x_1613_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v_unused_1634_ = lean_ctor_get(v___x_1613_, 0);
                        lean_dec(v_unused_1634_);
                        v___x_1628_ = v___x_1613_;
                        v_isShared_1629_ = v_isSharedCheck_1633_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1626_);
                        lean_dec(v___x_1613_);
                        v___x_1628_ = lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1633_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1612_ == 0 {
                    lean_ctor_set(v___x_1611_, 0, v_a_1614_);
                    v___x_1620_ = v___x_1611_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1614_);
                    v___x_1620_ = v_reuseFailAlloc_1624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1618_ == 0 {
                    lean_ctor_set(v___x_1617_, 0, v___x_1620_);
                    v___x_1622_ = v___x_1617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_a_1615_);
                    v___x_1622_ = v_reuseFailAlloc_1623_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1622_;
            }
            5 => {
                if v_isShared_1629_ == 0 {
                    lean_ctor_set_tag(v___x_1628_, 0);
                    lean_ctor_set(v___x_1628_, 0, v___x_1607_);
                    v___x_1631_ = v___x_1628_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1607_);
                    lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_a_1626_);
                    v___x_1631_ = v_reuseFailAlloc_1632_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_mergeErrors___redArg(
    mut v_x_u2081_1636_: *mut LeanObject,
    mut v_x_u2082_1637_: *mut LeanObject,
    mut v_f_1638_: *mut LeanObject,
    mut v_es_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1648_: u8 = 0;
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v_a_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut v_unused_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1672_: u8 = 0;
    let mut v_unused_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1640_ = lean_apply_1(v_x_u2081_1636_, v_es_1639_);
                if lean_obj_tag(v___x_1640_) == 0 {
                    v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
                    lean_inc(v_a_1641_);
                    v_a_1642_ = lean_ctor_get(v___x_1640_, 1);
                    lean_inc(v_a_1642_);
                    lean_dec_ref_known(v___x_1640_, 2);
                    v___x_1643_ = lean_apply_1(v_x_u2082_1637_, v_a_1642_);
                    if lean_obj_tag(v___x_1643_) == 0 {
                        v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
                        v_a_1645_ = lean_ctor_get(v___x_1643_, 1);
                        v_isSharedCheck_1653_ = (!lean_is_exclusive(v___x_1643_)) as u8;
                        if v_isSharedCheck_1653_ == 0 {
                            v___x_1647_ = v___x_1643_;
                            v_isShared_1648_ = v_isSharedCheck_1653_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1645_);
                            lean_inc(v_a_1644_);
                            lean_dec(v___x_1643_);
                            v___x_1647_ = lean_box(0);
                            v_isShared_1648_ = v_isSharedCheck_1653_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1641_);
                        lean_dec(v_f_1638_);
                        v_a_1654_ = lean_ctor_get(v___x_1643_, 1);
                        v_isSharedCheck_1662_ = (!lean_is_exclusive(v___x_1643_)) as u8;
                        if v_isSharedCheck_1662_ == 0 {
                            v_unused_1663_ = lean_ctor_get(v___x_1643_, 0);
                            lean_dec(v_unused_1663_);
                            v___x_1656_ = v___x_1643_;
                            v_isShared_1657_ = v_isSharedCheck_1662_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1654_);
                            lean_dec(v___x_1643_);
                            v___x_1656_ = lean_box(0);
                            v_isShared_1657_ = v_isSharedCheck_1662_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_f_1638_);
                    lean_dec_ref(v_x_u2082_1637_);
                    v_a_1664_ = lean_ctor_get(v___x_1640_, 1);
                    v_isSharedCheck_1672_ = (!lean_is_exclusive(v___x_1640_)) as u8;
                    if v_isSharedCheck_1672_ == 0 {
                        v_unused_1673_ = lean_ctor_get(v___x_1640_, 0);
                        lean_dec(v_unused_1673_);
                        v___x_1666_ = v___x_1640_;
                        v_isShared_1667_ = v_isSharedCheck_1672_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1664_);
                        lean_dec(v___x_1640_);
                        v___x_1666_ = lean_box(0);
                        v_isShared_1667_ = v_isSharedCheck_1672_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1649_ = lean_apply_2(v_f_1638_, v_a_1641_, v_a_1644_);
                if v_isShared_1648_ == 0 {
                    lean_ctor_set(v___x_1647_, 0, v___x_1649_);
                    v___x_1651_ = v___x_1647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
                    lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_a_1645_);
                    v___x_1651_ = v_reuseFailAlloc_1652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1651_;
            }
            3 => {
                v___x_1658_ = lean_box(0);
                if v_isShared_1657_ == 0 {
                    lean_ctor_set(v___x_1656_, 0, v___x_1658_);
                    v___x_1660_ = v___x_1656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
                    lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_a_1654_);
                    v___x_1660_ = v_reuseFailAlloc_1661_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1660_;
            }
            5 => {
                v___x_1668_ = lean_box(0);
                if v_isShared_1667_ == 0 {
                    lean_ctor_set(v___x_1666_, 0, v___x_1668_);
                    v___x_1670_ = v___x_1666_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
                    lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1664_);
                    v___x_1670_ = v_reuseFailAlloc_1671_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_mergeErrors(
    mut v_00_u03b1_1674_: *mut LeanObject,
    mut v_00_u03b2_1675_: *mut LeanObject,
    mut v_00_u03b3_1676_: *mut LeanObject,
    mut v_x_u2081_1677_: *mut LeanObject,
    mut v_x_u2082_1678_: *mut LeanObject,
    mut v_f_1679_: *mut LeanObject,
    mut v_es_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v___x_1681_ =
        l_Lake_Toml_mergeErrors___redArg(v_x_u2081_1677_, v_x_u2082_1678_, v_f_1679_, v_es_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Lake_Toml_logDecodeErrorAt(
    mut v_ref_1682_: *mut LeanObject,
    mut v_msg_1683_: *mut LeanObject,
    mut v_es_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = lean_box(0);
    v___x_1686_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1686_, 0, v_ref_1682_);
    lean_ctor_set(v___x_1686_, 1, v_msg_1683_);
    v___x_1687_ = lean_array_push(v_es_1684_, v___x_1686_);
    v___x_1688_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1688_, 0, v___x_1685_);
    lean_ctor_set(v___x_1688_, 1, v___x_1687_);
    return v___x_1688_;
}
pub unsafe fn l_Lake_Toml_throwDecodeErrorAt___redArg(
    mut v_ref_1689_: *mut LeanObject,
    mut v_msg_1690_: *mut LeanObject,
    mut v_es_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    v___x_1692_ = lean_box(0);
    v___x_1693_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1693_, 0, v_ref_1689_);
    lean_ctor_set(v___x_1693_, 1, v_msg_1690_);
    v___x_1694_ = lean_array_push(v_es_1691_, v___x_1693_);
    v___x_1695_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1695_, 0, v___x_1692_);
    lean_ctor_set(v___x_1695_, 1, v___x_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Lake_Toml_throwDecodeErrorAt(
    mut v_00_u03b1_1696_: *mut LeanObject,
    mut v_ref_1697_: *mut LeanObject,
    mut v_msg_1698_: *mut LeanObject,
    mut v_es_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    v___x_1700_ = lean_box(0);
    v___x_1701_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1701_, 0, v_ref_1697_);
    lean_ctor_set(v___x_1701_, 1, v_msg_1698_);
    v___x_1702_ = lean_array_push(v_es_1699_, v___x_1701_);
    v___x_1703_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1703_, 0, v___x_1700_);
    lean_ctor_set(v___x_1703_, 1, v___x_1702_);
    return v___x_1703_;
}
pub unsafe fn l_Lake_Toml_decodeArray___redArg___lam__0(
    mut v_dec_1705_: *mut LeanObject,
    mut v_x1_1706_: *mut LeanObject,
    mut v_x2_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1709_ = lean_apply_1(v_dec_1705_, v_x2_1707_);
    v___x_1710_ = l_Lake_Toml_decodeArray___redArg___lam__0___closed__0;
    v___x_1711_ =
        l_Lake_Toml_mergeErrors___redArg(v_x1_1706_, v___x_1709_, v___x_1710_, v___y_1708_);
    return v___x_1711_;
}
pub unsafe fn l_Lake_Toml_decodeArray___redArg(
    mut v_dec_1731_: *mut LeanObject,
    mut v_vs_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    v___x_1734_ = lean_array_get_size(v_vs_1732_);
    v___x_1735_ = lean_mk_empty_array_with_capacity(v___x_1734_);
    v___x_1736_ = lean_unsigned_to_nat(0);
    v___x_1737_ = l_Lake_Toml_decodeArray___redArg___closed__9;
    v___x_1738_ = lean_nat_dec_lt(v___x_1736_, v___x_1734_);
    if v___x_1738_ == 0 {
        let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_vs_1732_);
        lean_dec_ref(v_dec_1731_);
        v___x_1739_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1739_, 0, v___x_1735_);
        lean_ctor_set(v___x_1739_, 1, v_a_1733_);
        return v___x_1739_;
    } else {
        let mut v___f_1740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1742_: u8 = 0;
        v___f_1740_ = lean_alloc_closure(
            l_Lake_Toml_decodeArray___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_1740_, 0, v_dec_1731_);
        lean_inc_ref(v___x_1735_);
        v___x_1741_ = lean_alloc_closure(l_EStateM_pure as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___x_1741_, 0, lean_box(0));
        lean_closure_set(v___x_1741_, 1, lean_box(0));
        lean_closure_set(v___x_1741_, 2, lean_box(0));
        lean_closure_set(v___x_1741_, 3, v___x_1735_);
        v___x_1742_ = lean_nat_dec_le(v___x_1734_, v___x_1734_);
        if v___x_1742_ == 0 {
            if v___x_1738_ == 0 {
                let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_1741_);
                lean_dec_ref(v___f_1740_);
                lean_dec_ref(v_vs_1732_);
                v___x_1743_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1743_, 0, v___x_1735_);
                lean_ctor_set(v___x_1743_, 1, v_a_1733_);
                return v___x_1743_;
            } else {
                let mut v___x_1744_: usize = 0;
                let mut v___x_1745_: usize = 0;
                let mut v___x_133__overap_1746_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_1735_);
                v___x_1744_ = 0usize;
                v___x_1745_ = lean_usize_of_nat(v___x_1734_);
                v___x_133__overap_1746_ =
                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_1737_,
                        v___f_1740_,
                        v_vs_1732_,
                        v___x_1744_,
                        v___x_1745_,
                        v___x_1741_,
                    );
                v___x_1747_ = lean_apply_1(v___x_133__overap_1746_, v_a_1733_);
                return v___x_1747_;
            }
        } else {
            let mut v___x_1748_: usize = 0;
            let mut v___x_1749_: usize = 0;
            let mut v___x_138__overap_1750_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_1735_);
            v___x_1748_ = 0usize;
            v___x_1749_ = lean_usize_of_nat(v___x_1734_);
            v___x_138__overap_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_1737_,
                v___f_1740_,
                v_vs_1732_,
                v___x_1748_,
                v___x_1749_,
                v___x_1741_,
            );
            v___x_1751_ = lean_apply_1(v___x_138__overap_1750_, v_a_1733_);
            return v___x_1751_;
        }
    }
}
pub unsafe fn l_Lake_Toml_decodeArray(
    mut v_00_u03b1_1752_: *mut LeanObject,
    mut v_dec_1753_: *mut LeanObject,
    mut v_vs_1754_: *mut LeanObject,
    mut v_a_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Lake_Toml_decodeArray___redArg(v_dec_1753_, v_vs_1754_, v_a_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Lake_Toml_Value_decodeString(
    mut v_v_1760_: *mut LeanObject,
    mut v_a_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_unused_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1760_) == 0 {
                    v_s_1769_ = lean_ctor_get(v_v_1760_, 1);
                    v_isSharedCheck_1776_ = (!lean_is_exclusive(v_v_1760_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v_unused_1777_ = lean_ctor_get(v_v_1760_, 0);
                        lean_dec(v_unused_1777_);
                        v___x_1771_ = v_v_1760_;
                        v_isShared_1772_ = v_isSharedCheck_1776_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_s_1769_);
                        lean_dec(v_v_1760_);
                        v___x_1771_ = lean_box(0);
                        v_isShared_1772_ = v_isSharedCheck_1776_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_1778_ = lean_ctor_get(v_v_1760_, 0);
                    lean_inc(v_ref_1778_);
                    lean_dec_ref(v_v_1760_);
                    v___y_1763_ = v_ref_1778_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1764_ = l_Lake_Toml_Value_decodeString___closed__0;
                v___x_1765_ = lean_box(0);
                v___x_1766_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1766_, 0, v___y_1763_);
                lean_ctor_set(v___x_1766_, 1, v___x_1764_);
                v___x_1767_ = lean_array_push(v_a_1761_, v___x_1766_);
                v___x_1768_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1768_, 0, v___x_1765_);
                lean_ctor_set(v___x_1768_, 1, v___x_1767_);
                return v___x_1768_;
            }
            2 => {
                if v_isShared_1772_ == 0 {
                    lean_ctor_set(v___x_1771_, 1, v_a_1761_);
                    lean_ctor_set(v___x_1771_, 0, v_s_1769_);
                    v___x_1774_ = v___x_1771_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_s_1769_);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_a_1761_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_instDecodeTomlFilePath___lam__0(
    mut v_x_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_a_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1783_ = l_Lake_Toml_Value_decodeString(v_x_1781_, v___y_1782_);
                if lean_obj_tag(v___x_1783_) == 0 {
                    v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
                    v_a_1785_ = lean_ctor_get(v___x_1783_, 1);
                    v_isSharedCheck_1792_ = (!lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1787_ = v___x_1783_;
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1785_);
                        lean_inc(v_a_1784_);
                        lean_dec(v___x_1783_);
                        v___x_1787_ = lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1793_ = lean_ctor_get(v___x_1783_, 0);
                    v_a_1794_ = lean_ctor_get(v___x_1783_, 1);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1783_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1794_);
                        lean_inc(v_a_1793_);
                        lean_dec(v___x_1783_);
                        v___x_1796_ = lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1788_ == 0 {
                    v___x_1790_ = v___x_1787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1784_);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_a_1785_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1790_;
            }
            3 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1793_);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeName(
    mut v_v_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___y_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v_a_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_v_1805_);
                v___x_1807_ = l_Lake_Toml_Value_decodeString(v_v_1805_, v_a_1806_);
                if lean_obj_tag(v___x_1807_) == 0 {
                    v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
                    v_a_1809_ = lean_ctor_get(v___x_1807_, 1);
                    v_isSharedCheck_1825_ = (!lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1825_ == 0 {
                        v___x_1811_ = v___x_1807_;
                        v_isShared_1812_ = v_isSharedCheck_1825_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1809_);
                        lean_inc(v_a_1808_);
                        lean_dec(v___x_1807_);
                        v___x_1811_ = lean_box(0);
                        v_isShared_1812_ = v_isSharedCheck_1825_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_v_1805_);
                    v_a_1826_ = lean_ctor_get(v___x_1807_, 0);
                    v_a_1827_ = lean_ctor_get(v___x_1807_, 1);
                    v_isSharedCheck_1834_ = (!lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v___x_1829_ = v___x_1807_;
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1827_);
                        lean_inc(v_a_1826_);
                        lean_dec(v___x_1807_);
                        v___x_1829_ = lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1822_ = l_String_toName(v_a_1808_);
                if lean_obj_tag(v___x_1822_) == 0 {
                    v_ref_1823_ = lean_ctor_get(v_v_1805_, 0);
                    lean_inc(v_ref_1823_);
                    lean_dec_ref(v_v_1805_);
                    v___y_1814_ = v_ref_1823_;
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_1811_);
                    lean_dec_ref(v_v_1805_);
                    v___x_1824_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1824_, 0, v___x_1822_);
                    lean_ctor_set(v___x_1824_, 1, v_a_1809_);
                    return v___x_1824_;
                }
            }
            2 => {
                v___x_1815_ = l_Lake_Toml_Value_decodeName___closed__0;
                v___x_1816_ = lean_box(0);
                v___x_1817_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1817_, 0, v___y_1814_);
                lean_ctor_set(v___x_1817_, 1, v___x_1815_);
                v___x_1818_ = lean_array_push(v_a_1809_, v___x_1817_);
                if v_isShared_1812_ == 0 {
                    lean_ctor_set_tag(v___x_1811_, 1);
                    lean_ctor_set(v___x_1811_, 1, v___x_1818_);
                    lean_ctor_set(v___x_1811_, 0, v___x_1816_);
                    v___x_1820_ = v___x_1811_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1816_);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1818_);
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1820_;
            }
            4 => {
                if v_isShared_1830_ == 0 {
                    v___x_1832_ = v___x_1829_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1826_);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_a_1827_);
                    v___x_1832_ = v_reuseFailAlloc_1833_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeInt(
    mut v_v_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1854_: u8 = 0;
    let mut v_unused_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1838_) == 1 {
                    v_n_1847_ = lean_ctor_get(v_v_1838_, 1);
                    v_isSharedCheck_1854_ = (!lean_is_exclusive(v_v_1838_)) as u8;
                    if v_isSharedCheck_1854_ == 0 {
                        v_unused_1855_ = lean_ctor_get(v_v_1838_, 0);
                        lean_dec(v_unused_1855_);
                        v___x_1849_ = v_v_1838_;
                        v_isShared_1850_ = v_isSharedCheck_1854_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_n_1847_);
                        lean_dec(v_v_1838_);
                        v___x_1849_ = lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1854_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_1856_ = lean_ctor_get(v_v_1838_, 0);
                    lean_inc(v_ref_1856_);
                    lean_dec_ref(v_v_1838_);
                    v___y_1841_ = v_ref_1856_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1842_ = l_Lake_Toml_Value_decodeInt___closed__0;
                v___x_1843_ = lean_box(0);
                v___x_1844_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1844_, 0, v___y_1841_);
                lean_ctor_set(v___x_1844_, 1, v___x_1842_);
                v___x_1845_ = lean_array_push(v_a_1839_, v___x_1844_);
                v___x_1846_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1846_, 0, v___x_1843_);
                lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                return v___x_1846_;
            }
            2 => {
                if v_isShared_1850_ == 0 {
                    lean_ctor_set_tag(v___x_1849_, 0);
                    lean_ctor_set(v___x_1849_, 1, v_a_1839_);
                    lean_ctor_set(v___x_1849_, 0, v_n_1847_);
                    v___x_1852_ = v___x_1849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_n_1847_);
                    lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_a_1839_);
                    v___x_1852_ = v_reuseFailAlloc_1853_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_Toml_Value_decodeNat___closed__1() -> *mut LeanObject {
    let mut v_natZero_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1861_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_1860_ = lean_unsigned_to_nat(0);
    v_intZero_1861_ = lean_nat_to_int(v_natZero_1860_);
    return v_intZero_1861_;
}
pub unsafe fn l_Lake_Toml_Value_decodeNat(
    mut v_x_1862_: *mut LeanObject,
    mut v_a_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v_intZero_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1878_: u8 = 0;
    let mut v_a_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1883_: u8 = 0;
    let mut v_ref_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1862_) == 1 {
                    v_ref_1872_ = lean_ctor_get(v_x_1862_, 0);
                    v_n_1873_ = lean_ctor_get(v_x_1862_, 1);
                    v_isSharedCheck_1883_ = (!lean_is_exclusive(v_x_1862_)) as u8;
                    if v_isSharedCheck_1883_ == 0 {
                        v___x_1875_ = v_x_1862_;
                        v_isShared_1876_ = v_isSharedCheck_1883_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_n_1873_);
                        lean_inc(v_ref_1872_);
                        lean_dec(v_x_1862_);
                        v___x_1875_ = lean_box(0);
                        v_isShared_1876_ = v_isSharedCheck_1883_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_1884_ = lean_ctor_get(v_x_1862_, 0);
                    lean_inc(v_ref_1884_);
                    lean_dec_ref(v_x_1862_);
                    v___y_1865_ = v_a_1863_;
                    v___y_1866_ = v_ref_1884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1867_ = l_Lake_Toml_Value_decodeNat___closed__0;
                v___x_1868_ = lean_box(0);
                v___x_1869_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v___y_1866_);
                lean_ctor_set(v___x_1869_, 1, v___x_1867_);
                v___x_1870_ = lean_array_push(v___y_1865_, v___x_1869_);
                v___x_1871_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1871_, 0, v___x_1868_);
                lean_ctor_set(v___x_1871_, 1, v___x_1870_);
                return v___x_1871_;
            }
            2 => {
                v_intZero_1877_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Toml_Value_decodeNat___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_Toml_Value_decodeNat___closed__1_once),
                    _init_l_Lake_Toml_Value_decodeNat___closed__1,
                );
                v_isNeg_1878_ = lean_int_dec_lt(v_n_1873_, v_intZero_1877_);
                if v_isNeg_1878_ == 0 {
                    lean_dec(v_ref_1872_);
                    v_a_1879_ = lean_nat_abs(v_n_1873_);
                    lean_dec(v_n_1873_);
                    if v_isShared_1876_ == 0 {
                        lean_ctor_set_tag(v___x_1875_, 0);
                        lean_ctor_set(v___x_1875_, 1, v_a_1863_);
                        lean_ctor_set(v___x_1875_, 0, v_a_1879_);
                        v___x_1881_ = v___x_1875_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1879_);
                        lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_a_1863_);
                        v___x_1881_ = v_reuseFailAlloc_1882_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1875_);
                    lean_dec(v_n_1873_);
                    v___y_1865_ = v_a_1863_;
                    v___y_1866_ = v_ref_1872_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_1881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeFloat(
    mut v_v_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1897_: f64 = 0.0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1888_) == 2 {
                    v_n_1897_ = lean_ctor_get_float(
                        v_v_1888_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_v_1888_, 1);
                    v___x_1898_ = lean_box_float(v_n_1897_);
                    v___x_1899_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1899_, 0, v___x_1898_);
                    lean_ctor_set(v___x_1899_, 1, v_a_1889_);
                    return v___x_1899_;
                } else {
                    v_ref_1900_ = lean_ctor_get(v_v_1888_, 0);
                    lean_inc(v_ref_1900_);
                    lean_dec_ref(v_v_1888_);
                    v___y_1891_ = v_ref_1900_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1892_ = l_Lake_Toml_Value_decodeFloat___closed__0;
                v___x_1893_ = lean_box(0);
                v___x_1894_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1894_, 0, v___y_1891_);
                lean_ctor_set(v___x_1894_, 1, v___x_1892_);
                v___x_1895_ = lean_array_push(v_a_1889_, v___x_1894_);
                v___x_1896_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1896_, 0, v___x_1893_);
                lean_ctor_set(v___x_1896_, 1, v___x_1895_);
                return v___x_1896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeBool(
    mut v_v_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1904_) == 3 {
                    v_b_1913_ = lean_ctor_get_uint8(
                        v_v_1904_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_v_1904_, 1);
                    v___x_1914_ = lean_box((v_b_1913_) as usize);
                    v___x_1915_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                    lean_ctor_set(v___x_1915_, 1, v_a_1905_);
                    return v___x_1915_;
                } else {
                    v_ref_1916_ = lean_ctor_get(v_v_1904_, 0);
                    lean_inc(v_ref_1916_);
                    lean_dec_ref(v_v_1904_);
                    v___y_1907_ = v_ref_1916_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1908_ = l_Lake_Toml_Value_decodeBool___closed__0;
                v___x_1909_ = lean_box(0);
                v___x_1910_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1910_, 0, v___y_1907_);
                lean_ctor_set(v___x_1910_, 1, v___x_1908_);
                v___x_1911_ = lean_array_push(v_a_1905_, v___x_1910_);
                v___x_1912_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1912_, 0, v___x_1909_);
                lean_ctor_set(v___x_1912_, 1, v___x_1911_);
                return v___x_1912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeDateTime(
    mut v_v_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dt_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1936_: u8 = 0;
    let mut v_unused_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1920_) == 4 {
                    v_dt_1929_ = lean_ctor_get(v_v_1920_, 1);
                    v_isSharedCheck_1936_ = (!lean_is_exclusive(v_v_1920_)) as u8;
                    if v_isSharedCheck_1936_ == 0 {
                        v_unused_1937_ = lean_ctor_get(v_v_1920_, 0);
                        lean_dec(v_unused_1937_);
                        v___x_1931_ = v_v_1920_;
                        v_isShared_1932_ = v_isSharedCheck_1936_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_dt_1929_);
                        lean_dec(v_v_1920_);
                        v___x_1931_ = lean_box(0);
                        v_isShared_1932_ = v_isSharedCheck_1936_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_1938_ = lean_ctor_get(v_v_1920_, 0);
                    lean_inc(v_ref_1938_);
                    lean_dec_ref(v_v_1920_);
                    v___y_1923_ = v_ref_1938_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1924_ = l_Lake_Toml_Value_decodeDateTime___closed__0;
                v___x_1925_ = lean_box(0);
                v___x_1926_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1926_, 0, v___y_1923_);
                lean_ctor_set(v___x_1926_, 1, v___x_1924_);
                v___x_1927_ = lean_array_push(v_a_1921_, v___x_1926_);
                v___x_1928_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1928_, 0, v___x_1925_);
                lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                return v___x_1928_;
            }
            2 => {
                if v_isShared_1932_ == 0 {
                    lean_ctor_set_tag(v___x_1931_, 0);
                    lean_ctor_set(v___x_1931_, 1, v_a_1921_);
                    lean_ctor_set(v___x_1931_, 0, v_dt_1929_);
                    v___x_1934_ = v___x_1931_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_dt_1929_);
                    lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1921_);
                    v___x_1934_ = v_reuseFailAlloc_1935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeValueArray(
    mut v_v_1942_: *mut LeanObject,
    mut v_a_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1954_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1958_: u8 = 0;
    let mut v_unused_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_1942_) == 5 {
                    v_xs_1951_ = lean_ctor_get(v_v_1942_, 1);
                    v_isSharedCheck_1958_ = (!lean_is_exclusive(v_v_1942_)) as u8;
                    if v_isSharedCheck_1958_ == 0 {
                        v_unused_1959_ = lean_ctor_get(v_v_1942_, 0);
                        lean_dec(v_unused_1959_);
                        v___x_1953_ = v_v_1942_;
                        v_isShared_1954_ = v_isSharedCheck_1958_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_xs_1951_);
                        lean_dec(v_v_1942_);
                        v___x_1953_ = lean_box(0);
                        v_isShared_1954_ = v_isSharedCheck_1958_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_1960_ = lean_ctor_get(v_v_1942_, 0);
                    lean_inc(v_ref_1960_);
                    lean_dec_ref(v_v_1942_);
                    v___y_1945_ = v_ref_1960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1946_ = l_Lake_Toml_Value_decodeValueArray___closed__0;
                v___x_1947_ = lean_box(0);
                v___x_1948_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1948_, 0, v___y_1945_);
                lean_ctor_set(v___x_1948_, 1, v___x_1946_);
                v___x_1949_ = lean_array_push(v_a_1943_, v___x_1948_);
                v___x_1950_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1950_, 0, v___x_1947_);
                lean_ctor_set(v___x_1950_, 1, v___x_1949_);
                return v___x_1950_;
            }
            2 => {
                if v_isShared_1954_ == 0 {
                    lean_ctor_set_tag(v___x_1953_, 0);
                    lean_ctor_set(v___x_1953_, 1, v_a_1943_);
                    lean_ctor_set(v___x_1953_, 0, v_xs_1951_);
                    v___x_1956_ = v___x_1953_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_xs_1951_);
                    lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_a_1943_);
                    v___x_1956_ = v_reuseFailAlloc_1957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeArray___redArg(
    mut v_dec_1961_: *mut LeanObject,
    mut v_v_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1964_ = l_Lake_Toml_Value_decodeValueArray(v_v_1962_, v_a_1963_);
                if lean_obj_tag(v___x_1964_) == 0 {
                    v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
                    lean_inc(v_a_1965_);
                    v_a_1966_ = lean_ctor_get(v___x_1964_, 1);
                    lean_inc(v_a_1966_);
                    lean_dec_ref_known(v___x_1964_, 2);
                    v___x_1967_ =
                        l_Lake_Toml_decodeArray___redArg(v_dec_1961_, v_a_1965_, v_a_1966_);
                    return v___x_1967_;
                } else {
                    lean_dec_ref(v_dec_1961_);
                    v_a_1968_ = lean_ctor_get(v___x_1964_, 0);
                    v_a_1969_ = lean_ctor_get(v___x_1964_, 1);
                    v_isSharedCheck_1976_ = (!lean_is_exclusive(v___x_1964_)) as u8;
                    if v_isSharedCheck_1976_ == 0 {
                        v___x_1971_ = v___x_1964_;
                        v_isShared_1972_ = v_isSharedCheck_1976_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1969_);
                        lean_inc(v_a_1968_);
                        lean_dec(v___x_1964_);
                        v___x_1971_ = lean_box(0);
                        v_isShared_1972_ = v_isSharedCheck_1976_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1972_ == 0 {
                    v___x_1974_ = v___x_1971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1968_);
                    lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_a_1969_);
                    v___x_1974_ = v_reuseFailAlloc_1975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeArray(
    mut v_00_u03b1_1977_: *mut LeanObject,
    mut v_dec_1978_: *mut LeanObject,
    mut v_v_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1989_: u8 = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1981_ = l_Lake_Toml_Value_decodeValueArray(v_v_1979_, v_a_1980_);
                if lean_obj_tag(v___x_1981_) == 0 {
                    v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
                    lean_inc(v_a_1982_);
                    v_a_1983_ = lean_ctor_get(v___x_1981_, 1);
                    lean_inc(v_a_1983_);
                    lean_dec_ref_known(v___x_1981_, 2);
                    v___x_1984_ =
                        l_Lake_Toml_decodeArray___redArg(v_dec_1978_, v_a_1982_, v_a_1983_);
                    return v___x_1984_;
                } else {
                    lean_dec_ref(v_dec_1978_);
                    v_a_1985_ = lean_ctor_get(v___x_1981_, 0);
                    v_a_1986_ = lean_ctor_get(v___x_1981_, 1);
                    v_isSharedCheck_1993_ = (!lean_is_exclusive(v___x_1981_)) as u8;
                    if v_isSharedCheck_1993_ == 0 {
                        v___x_1988_ = v___x_1981_;
                        v_isShared_1989_ = v_isSharedCheck_1993_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1986_);
                        lean_inc(v_a_1985_);
                        lean_dec(v___x_1981_);
                        v___x_1988_ = lean_box(0);
                        v_isShared_1989_ = v_isSharedCheck_1993_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1989_ == 0 {
                    v___x_1991_ = v___x_1988_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1985_);
                    lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_a_1986_);
                    v___x_1991_ = v_reuseFailAlloc_1992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_instDecodeTomlArray___redArg(
    mut v_inst_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = lean_alloc_closure(
        l_Lake_Toml_Value_decodeArray as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_1995_, 0, lean_box(0));
    lean_closure_set(v___x_1995_, 1, v_inst_1994_);
    return v___x_1995_;
}
pub unsafe fn l_Lake_Toml_Value_instDecodeTomlArray(
    mut v_00_u03b1_1996_: *mut LeanObject,
    mut v_inst_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    v___x_1998_ = lean_alloc_closure(
        l_Lake_Toml_Value_decodeArray as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_1998_, 0, lean_box(0));
    lean_closure_set(v___x_1998_, 1, v_inst_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Lake_Toml_Value_decodeArrayOrSingleton___redArg(
    mut v_dec_1999_: *mut LeanObject,
    mut v_v_2000_: *mut LeanObject,
    mut v_a_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_xs_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut v_a_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2000_) == 5 {
                    v_xs_2002_ = lean_ctor_get(v_v_2000_, 1);
                    lean_inc_ref(v_xs_2002_);
                    lean_dec_ref_known(v_v_2000_, 2);
                    v___x_2003_ =
                        l_Lake_Toml_decodeArray___redArg(v_dec_1999_, v_xs_2002_, v_a_2001_);
                    return v___x_2003_;
                } else {
                    v___x_2004_ = lean_apply_2(v_dec_1999_, v_v_2000_, v_a_2001_);
                    if lean_obj_tag(v___x_2004_) == 0 {
                        v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
                        v_a_2006_ = lean_ctor_get(v___x_2004_, 1);
                        v_isSharedCheck_2016_ = (!lean_is_exclusive(v___x_2004_)) as u8;
                        if v_isSharedCheck_2016_ == 0 {
                            v___x_2008_ = v___x_2004_;
                            v_isShared_2009_ = v_isSharedCheck_2016_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2006_);
                            lean_inc(v_a_2005_);
                            lean_dec(v___x_2004_);
                            v___x_2008_ = lean_box(0);
                            v_isShared_2009_ = v_isSharedCheck_2016_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2017_ = lean_ctor_get(v___x_2004_, 0);
                        v_a_2018_ = lean_ctor_get(v___x_2004_, 1);
                        v_isSharedCheck_2025_ = (!lean_is_exclusive(v___x_2004_)) as u8;
                        if v_isSharedCheck_2025_ == 0 {
                            v___x_2020_ = v___x_2004_;
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2018_);
                            lean_inc(v_a_2017_);
                            lean_dec(v___x_2004_);
                            v___x_2020_ = lean_box(0);
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2010_ = lean_unsigned_to_nat(1);
                v___x_2011_ = lean_mk_empty_array_with_capacity(v___x_2010_);
                v___x_2012_ = lean_array_push(v___x_2011_, v_a_2005_);
                if v_isShared_2009_ == 0 {
                    lean_ctor_set(v___x_2008_, 0, v___x_2012_);
                    v___x_2014_ = v___x_2008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
                    lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_a_2006_);
                    v___x_2014_ = v_reuseFailAlloc_2015_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2014_;
            }
            3 => {
                if v_isShared_2021_ == 0 {
                    v___x_2023_ = v___x_2020_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2017_);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_a_2018_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeArrayOrSingleton(
    mut v_00_u03b1_2026_: *mut LeanObject,
    mut v_dec_2027_: *mut LeanObject,
    mut v_v_2028_: *mut LeanObject,
    mut v_a_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_xs_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2053_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2028_) == 5 {
                    v_xs_2030_ = lean_ctor_get(v_v_2028_, 1);
                    lean_inc_ref(v_xs_2030_);
                    lean_dec_ref_known(v_v_2028_, 2);
                    v___x_2031_ =
                        l_Lake_Toml_decodeArray___redArg(v_dec_2027_, v_xs_2030_, v_a_2029_);
                    return v___x_2031_;
                } else {
                    v___x_2032_ = lean_apply_2(v_dec_2027_, v_v_2028_, v_a_2029_);
                    if lean_obj_tag(v___x_2032_) == 0 {
                        v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
                        v_a_2034_ = lean_ctor_get(v___x_2032_, 1);
                        v_isSharedCheck_2044_ = (!lean_is_exclusive(v___x_2032_)) as u8;
                        if v_isSharedCheck_2044_ == 0 {
                            v___x_2036_ = v___x_2032_;
                            v_isShared_2037_ = v_isSharedCheck_2044_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2034_);
                            lean_inc(v_a_2033_);
                            lean_dec(v___x_2032_);
                            v___x_2036_ = lean_box(0);
                            v_isShared_2037_ = v_isSharedCheck_2044_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2045_ = lean_ctor_get(v___x_2032_, 0);
                        v_a_2046_ = lean_ctor_get(v___x_2032_, 1);
                        v_isSharedCheck_2053_ = (!lean_is_exclusive(v___x_2032_)) as u8;
                        if v_isSharedCheck_2053_ == 0 {
                            v___x_2048_ = v___x_2032_;
                            v_isShared_2049_ = v_isSharedCheck_2053_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2046_);
                            lean_inc(v_a_2045_);
                            lean_dec(v___x_2032_);
                            v___x_2048_ = lean_box(0);
                            v_isShared_2049_ = v_isSharedCheck_2053_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2038_ = lean_unsigned_to_nat(1);
                v___x_2039_ = lean_mk_empty_array_with_capacity(v___x_2038_);
                v___x_2040_ = lean_array_push(v___x_2039_, v_a_2033_);
                if v_isShared_2037_ == 0 {
                    lean_ctor_set(v___x_2036_, 0, v___x_2040_);
                    v___x_2042_ = v___x_2036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2034_);
                    v___x_2042_ = v_reuseFailAlloc_2043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2042_;
            }
            3 => {
                if v_isShared_2049_ == 0 {
                    v___x_2051_ = v___x_2048_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2045_);
                    lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_a_2046_);
                    v___x_2051_ = v_reuseFailAlloc_2052_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_decodeTable(
    mut v_v_2055_: *mut LeanObject,
    mut v_a_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v_unused_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2055_) == 6 {
                    v_xs_2064_ = lean_ctor_get(v_v_2055_, 1);
                    v_isSharedCheck_2071_ = (!lean_is_exclusive(v_v_2055_)) as u8;
                    if v_isSharedCheck_2071_ == 0 {
                        v_unused_2072_ = lean_ctor_get(v_v_2055_, 0);
                        lean_dec(v_unused_2072_);
                        v___x_2066_ = v_v_2055_;
                        v_isShared_2067_ = v_isSharedCheck_2071_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_xs_2064_);
                        lean_dec(v_v_2055_);
                        v___x_2066_ = lean_box(0);
                        v_isShared_2067_ = v_isSharedCheck_2071_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_2073_ = lean_ctor_get(v_v_2055_, 0);
                    lean_inc(v_ref_2073_);
                    lean_dec_ref(v_v_2055_);
                    v___y_2058_ = v_ref_2073_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2059_ = l_Lake_Toml_Value_decodeTable___closed__0;
                v___x_2060_ = lean_box(0);
                v___x_2061_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2061_, 0, v___y_2058_);
                lean_ctor_set(v___x_2061_, 1, v___x_2059_);
                v___x_2062_ = lean_array_push(v_a_2056_, v___x_2061_);
                v___x_2063_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2063_, 0, v___x_2060_);
                lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                return v___x_2063_;
            }
            2 => {
                if v_isShared_2067_ == 0 {
                    lean_ctor_set_tag(v___x_2066_, 0);
                    lean_ctor_set(v___x_2066_, 1, v_a_2056_);
                    lean_ctor_set(v___x_2066_, 0, v_xs_2064_);
                    v___x_2069_ = v___x_2066_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_xs_2064_);
                    lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_a_2056_);
                    v___x_2069_ = v_reuseFailAlloc_2070_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_decodeKeyval___redArg___lam__0(
    mut v_iniPos_2078_: *mut LeanObject,
    mut v_k_2079_: *mut LeanObject,
    mut v_i_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_x_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2083_: u8 = 0;
    let mut v_ref_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2088_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2083_ = lean_nat_dec_le(v_iniPos_2078_, v_i_2080_);
                if v___x_2083_ == 0 {
                    lean_dec(v_k_2079_);
                    return v_a_2081_;
                } else {
                    v_ref_2084_ = lean_ctor_get(v_a_2081_, 0);
                    v_msg_2085_ = lean_ctor_get(v_a_2081_, 1);
                    v_isSharedCheck_2098_ = (!lean_is_exclusive(v_a_2081_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_2087_ = v_a_2081_;
                        v_isShared_2088_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_msg_2085_);
                        lean_inc(v_ref_2084_);
                        lean_dec(v_a_2081_);
                        v___x_2087_ = lean_box(0);
                        v_isShared_2088_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2089_ = l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__0;
                v___x_2090_ = l_Lake_Toml_ppKey(v_k_2079_);
                v___x_2091_ = lean_string_append(v___x_2089_, v___x_2090_);
                lean_dec_ref(v___x_2090_);
                v___x_2092_ = l_Lake_Toml_decodeKeyval___redArg___lam__0___closed__1;
                v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
                v___x_2094_ = lean_string_append(v___x_2093_, v_msg_2085_);
                lean_dec_ref(v_msg_2085_);
                if v_isShared_2088_ == 0 {
                    lean_ctor_set(v___x_2087_, 1, v___x_2094_);
                    v___x_2096_ = v___x_2087_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_ref_2084_);
                    lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2094_);
                    v___x_2096_ = v_reuseFailAlloc_2097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed(
    mut v_iniPos_2099_: *mut LeanObject,
    mut v_k_2100_: *mut LeanObject,
    mut v_i_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
    mut v_x_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2104_: *mut LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Lake_Toml_decodeKeyval___redArg___lam__0(
        v_iniPos_2099_,
        v_k_2100_,
        v_i_2101_,
        v_a_2102_,
        v_x_2103_,
    );
    lean_dec(v_i_2101_);
    lean_dec(v_iniPos_2099_);
    return v_res_2104_;
}
pub unsafe fn l_Lake_Toml_decodeKeyval___redArg___lam__1(
    mut v___f_2105_: *mut LeanObject,
    mut v_es_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    v___x_2107_ = l_Lake_Toml_decodeArray___redArg___closed__9;
    v___x_2108_ = lean_array_get_size(v_es_2106_);
    v___x_2109_ = lean_unsigned_to_nat(0);
    v___x_2110_ = lean_mk_empty_array_with_capacity(v___x_2108_);
    v___x_2111_ = l_Array_mapFinIdxM_map___redArg(
        v___x_2107_,
        v_es_2106_,
        v___f_2105_,
        v___x_2108_,
        v___x_2109_,
        v___x_2110_,
    );
    return v___x_2111_;
}
pub unsafe fn l_Lake_Toml_decodeKeyval___redArg(
    mut v_dec_2112_: *mut LeanObject,
    mut v_k_2113_: *mut LeanObject,
    mut v_v_2114_: *mut LeanObject,
    mut v_es_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_iniPos_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2128_: u8 = 0;
    let mut v_a_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_iniPos_2116_ = lean_array_get_size(v_es_2115_);
                v___f_2117_ = lean_alloc_closure(
                    l_Lake_Toml_decodeKeyval___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_2117_, 0, v_iniPos_2116_);
                lean_closure_set(v___f_2117_, 1, v_k_2113_);
                v___x_2118_ = lean_apply_2(v_dec_2112_, v_v_2114_, v_es_2115_);
                if lean_obj_tag(v___x_2118_) == 0 {
                    v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
                    v_a_2120_ = lean_ctor_get(v___x_2118_, 1);
                    v_isSharedCheck_2128_ = (!lean_is_exclusive(v___x_2118_)) as u8;
                    if v_isSharedCheck_2128_ == 0 {
                        v___x_2122_ = v___x_2118_;
                        v_isShared_2123_ = v_isSharedCheck_2128_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2120_);
                        lean_inc(v_a_2119_);
                        lean_dec(v___x_2118_);
                        v___x_2122_ = lean_box(0);
                        v_isShared_2123_ = v_isSharedCheck_2128_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2129_ = lean_ctor_get(v___x_2118_, 0);
                    v_a_2130_ = lean_ctor_get(v___x_2118_, 1);
                    v_isSharedCheck_2138_ = (!lean_is_exclusive(v___x_2118_)) as u8;
                    if v_isSharedCheck_2138_ == 0 {
                        v___x_2132_ = v___x_2118_;
                        v_isShared_2133_ = v_isSharedCheck_2138_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2130_);
                        lean_inc(v_a_2129_);
                        lean_dec(v___x_2118_);
                        v___x_2132_ = lean_box(0);
                        v_isShared_2133_ = v_isSharedCheck_2138_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2124_ = l_Lake_Toml_decodeKeyval___redArg___lam__1(v___f_2117_, v_a_2120_);
                if v_isShared_2123_ == 0 {
                    lean_ctor_set(v___x_2122_, 1, v___x_2124_);
                    v___x_2126_ = v___x_2122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2119_);
                    lean_ctor_set(v_reuseFailAlloc_2127_, 1, v___x_2124_);
                    v___x_2126_ = v_reuseFailAlloc_2127_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2126_;
            }
            3 => {
                v___x_2134_ = l_Lake_Toml_decodeKeyval___redArg___lam__1(v___f_2117_, v_a_2130_);
                if v_isShared_2133_ == 0 {
                    lean_ctor_set(v___x_2132_, 1, v___x_2134_);
                    v___x_2136_ = v___x_2132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2129_);
                    lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2134_);
                    v___x_2136_ = v_reuseFailAlloc_2137_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_decodeKeyval(
    mut v_00_u03b1_2139_: *mut LeanObject,
    mut v_dec_2140_: *mut LeanObject,
    mut v_k_2141_: *mut LeanObject,
    mut v_v_2142_: *mut LeanObject,
    mut v_es_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2144_ = l_Lake_Toml_decodeKeyval___redArg(v_dec_2140_, v_k_2141_, v_v_2142_, v_es_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lake_Toml_Table_decodeValue(
    mut v_t_2147_: *mut LeanObject,
    mut v_k_2148_: *mut LeanObject,
    mut v_ref_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2164_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_unused_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2151_ = l_Lake_Toml_Table_decodeValue___closed__0;
                lean_inc(v_k_2148_);
                v___x_2152_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2151_, v_k_2148_, v_t_2147_);
                if lean_obj_tag(v___x_2152_) == 0 {
                    v___x_2153_ = l_Lake_Toml_Table_decodeValue___closed__1;
                    v___x_2154_ = l_Lake_Toml_ppKey(v_k_2148_);
                    v___x_2155_ = lean_string_append(v___x_2153_, v___x_2154_);
                    lean_dec_ref(v___x_2154_);
                    v___x_2156_ = lean_box(0);
                    v___x_2157_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2157_, 0, v_ref_2149_);
                    lean_ctor_set(v___x_2157_, 1, v___x_2155_);
                    v___x_2158_ = lean_array_push(v_a_2150_, v___x_2157_);
                    v___x_2159_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2159_, 0, v___x_2156_);
                    lean_ctor_set(v___x_2159_, 1, v___x_2158_);
                    return v___x_2159_;
                } else {
                    lean_dec(v_ref_2149_);
                    lean_dec(v_k_2148_);
                    v_val_2160_ = lean_ctor_get(v___x_2152_, 0);
                    lean_inc(v_val_2160_);
                    lean_dec_ref_known(v___x_2152_, 1);
                    v_snd_2161_ = lean_ctor_get(v_val_2160_, 1);
                    v_isSharedCheck_2168_ = (!lean_is_exclusive(v_val_2160_)) as u8;
                    if v_isSharedCheck_2168_ == 0 {
                        v_unused_2169_ = lean_ctor_get(v_val_2160_, 0);
                        lean_dec(v_unused_2169_);
                        v___x_2163_ = v_val_2160_;
                        v_isShared_2164_ = v_isSharedCheck_2168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2161_);
                        lean_dec(v_val_2160_);
                        v___x_2163_ = lean_box(0);
                        v_isShared_2164_ = v_isSharedCheck_2168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2164_ == 0 {
                    lean_ctor_set(v___x_2163_, 1, v_a_2150_);
                    lean_ctor_set(v___x_2163_, 0, v_snd_2161_);
                    v___x_2166_ = v___x_2163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_snd_2161_);
                    lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_a_2150_);
                    v___x_2166_ = v_reuseFailAlloc_2167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_decode___redArg(
    mut v_dec_2170_: *mut LeanObject,
    mut v_t_2171_: *mut LeanObject,
    mut v_k_2172_: *mut LeanObject,
    mut v_ref_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_k_2172_);
                v___x_2175_ =
                    l_Lake_Toml_Table_decodeValue(v_t_2171_, v_k_2172_, v_ref_2173_, v_a_2174_);
                if lean_obj_tag(v___x_2175_) == 0 {
                    v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
                    lean_inc(v_a_2176_);
                    v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
                    lean_inc(v_a_2177_);
                    lean_dec_ref_known(v___x_2175_, 2);
                    v___x_2178_ = l_Lake_Toml_decodeKeyval___redArg(
                        v_dec_2170_,
                        v_k_2172_,
                        v_a_2176_,
                        v_a_2177_,
                    );
                    return v___x_2178_;
                } else {
                    lean_dec(v_k_2172_);
                    lean_dec_ref(v_dec_2170_);
                    v_a_2179_ = lean_ctor_get(v___x_2175_, 0);
                    v_a_2180_ = lean_ctor_get(v___x_2175_, 1);
                    v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2175_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2182_ = v___x_2175_;
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2180_);
                        lean_inc(v_a_2179_);
                        lean_dec(v___x_2175_);
                        v___x_2182_ = lean_box(0);
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2183_ == 0 {
                    v___x_2185_ = v___x_2182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2179_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_decode(
    mut v_00_u03b1_2188_: *mut LeanObject,
    mut v_dec_2189_: *mut LeanObject,
    mut v_t_2190_: *mut LeanObject,
    mut v_k_2191_: *mut LeanObject,
    mut v_ref_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_k_2191_);
                v___x_2194_ =
                    l_Lake_Toml_Table_decodeValue(v_t_2190_, v_k_2191_, v_ref_2192_, v_a_2193_);
                if lean_obj_tag(v___x_2194_) == 0 {
                    v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
                    lean_inc(v_a_2195_);
                    v_a_2196_ = lean_ctor_get(v___x_2194_, 1);
                    lean_inc(v_a_2196_);
                    lean_dec_ref_known(v___x_2194_, 2);
                    v___x_2197_ = l_Lake_Toml_decodeKeyval___redArg(
                        v_dec_2189_,
                        v_k_2191_,
                        v_a_2195_,
                        v_a_2196_,
                    );
                    return v___x_2197_;
                } else {
                    lean_dec(v_k_2191_);
                    lean_dec_ref(v_dec_2189_);
                    v_a_2198_ = lean_ctor_get(v___x_2194_, 0);
                    v_a_2199_ = lean_ctor_get(v___x_2194_, 1);
                    v_isSharedCheck_2206_ = (!lean_is_exclusive(v___x_2194_)) as u8;
                    if v_isSharedCheck_2206_ == 0 {
                        v___x_2201_ = v___x_2194_;
                        v_isShared_2202_ = v_isSharedCheck_2206_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2199_);
                        lean_inc(v_a_2198_);
                        lean_dec(v___x_2194_);
                        v___x_2201_ = lean_box(0);
                        v_isShared_2202_ = v_isSharedCheck_2206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2202_ == 0 {
                    v___x_2204_ = v___x_2201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2198_);
                    lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_a_2199_);
                    v___x_2204_ = v_reuseFailAlloc_2205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_decode_x3f___redArg(
    mut v_dec_2207_: *mut LeanObject,
    mut v_t_2208_: *mut LeanObject,
    mut v_k_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v_snd_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut v_a_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2237_: u8 = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2211_ = l_Lake_Toml_Table_decodeValue___closed__0;
                lean_inc(v_k_2209_);
                v___x_2212_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2211_, v_k_2209_, v_t_2208_);
                if lean_obj_tag(v___x_2212_) == 0 {
                    lean_dec(v_k_2209_);
                    lean_dec_ref(v_dec_2207_);
                    v___x_2213_ = lean_box(0);
                    v___x_2214_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2214_, 0, v___x_2213_);
                    lean_ctor_set(v___x_2214_, 1, v_a_2210_);
                    return v___x_2214_;
                } else {
                    v_val_2215_ = lean_ctor_get(v___x_2212_, 0);
                    v_isSharedCheck_2242_ = (!lean_is_exclusive(v___x_2212_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2217_ = v___x_2212_;
                        v_isShared_2218_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2215_);
                        lean_dec(v___x_2212_);
                        v___x_2217_ = lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2242_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2219_ = lean_ctor_get(v_val_2215_, 1);
                lean_inc(v_snd_2219_);
                lean_dec(v_val_2215_);
                v___x_2220_ = l_Lake_Toml_decodeKeyval___redArg(
                    v_dec_2207_,
                    v_k_2209_,
                    v_snd_2219_,
                    v_a_2210_,
                );
                if lean_obj_tag(v___x_2220_) == 0 {
                    v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
                    v_a_2222_ = lean_ctor_get(v___x_2220_, 1);
                    v_isSharedCheck_2232_ = (!lean_is_exclusive(v___x_2220_)) as u8;
                    if v_isSharedCheck_2232_ == 0 {
                        v___x_2224_ = v___x_2220_;
                        v_isShared_2225_ = v_isSharedCheck_2232_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2222_);
                        lean_inc(v_a_2221_);
                        lean_dec(v___x_2220_);
                        v___x_2224_ = lean_box(0);
                        v_isShared_2225_ = v_isSharedCheck_2232_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2217_);
                    v_a_2233_ = lean_ctor_get(v___x_2220_, 0);
                    v_a_2234_ = lean_ctor_get(v___x_2220_, 1);
                    v_isSharedCheck_2241_ = (!lean_is_exclusive(v___x_2220_)) as u8;
                    if v_isSharedCheck_2241_ == 0 {
                        v___x_2236_ = v___x_2220_;
                        v_isShared_2237_ = v_isSharedCheck_2241_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2234_);
                        lean_inc(v_a_2233_);
                        lean_dec(v___x_2220_);
                        v___x_2236_ = lean_box(0);
                        v_isShared_2237_ = v_isSharedCheck_2241_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2218_ == 0 {
                    lean_ctor_set(v___x_2217_, 0, v_a_2221_);
                    v___x_2227_ = v___x_2217_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2221_);
                    v___x_2227_ = v_reuseFailAlloc_2231_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2225_ == 0 {
                    lean_ctor_set(v___x_2224_, 0, v___x_2227_);
                    v___x_2229_ = v___x_2224_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
                    lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_a_2222_);
                    v___x_2229_ = v_reuseFailAlloc_2230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2229_;
            }
            5 => {
                if v_isShared_2237_ == 0 {
                    v___x_2239_ = v___x_2236_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2233_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_a_2234_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_decode_x3f(
    mut v_00_u03b1_2243_: *mut LeanObject,
    mut v_dec_2244_: *mut LeanObject,
    mut v_t_2245_: *mut LeanObject,
    mut v_k_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2255_: u8 = 0;
    let mut v_snd_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut v_a_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2248_ = l_Lake_Toml_Table_decodeValue___closed__0;
                lean_inc(v_k_2246_);
                v___x_2249_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2248_, v_k_2246_, v_t_2245_);
                if lean_obj_tag(v___x_2249_) == 0 {
                    lean_dec(v_k_2246_);
                    lean_dec_ref(v_dec_2244_);
                    v___x_2250_ = lean_box(0);
                    v___x_2251_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                    lean_ctor_set(v___x_2251_, 1, v_a_2247_);
                    return v___x_2251_;
                } else {
                    v_val_2252_ = lean_ctor_get(v___x_2249_, 0);
                    v_isSharedCheck_2279_ = (!lean_is_exclusive(v___x_2249_)) as u8;
                    if v_isSharedCheck_2279_ == 0 {
                        v___x_2254_ = v___x_2249_;
                        v_isShared_2255_ = v_isSharedCheck_2279_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2252_);
                        lean_dec(v___x_2249_);
                        v___x_2254_ = lean_box(0);
                        v_isShared_2255_ = v_isSharedCheck_2279_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2256_ = lean_ctor_get(v_val_2252_, 1);
                lean_inc(v_snd_2256_);
                lean_dec(v_val_2252_);
                v___x_2257_ = l_Lake_Toml_decodeKeyval___redArg(
                    v_dec_2244_,
                    v_k_2246_,
                    v_snd_2256_,
                    v_a_2247_,
                );
                if lean_obj_tag(v___x_2257_) == 0 {
                    v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
                    v_a_2259_ = lean_ctor_get(v___x_2257_, 1);
                    v_isSharedCheck_2269_ = (!lean_is_exclusive(v___x_2257_)) as u8;
                    if v_isSharedCheck_2269_ == 0 {
                        v___x_2261_ = v___x_2257_;
                        v_isShared_2262_ = v_isSharedCheck_2269_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2259_);
                        lean_inc(v_a_2258_);
                        lean_dec(v___x_2257_);
                        v___x_2261_ = lean_box(0);
                        v_isShared_2262_ = v_isSharedCheck_2269_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2254_);
                    v_a_2270_ = lean_ctor_get(v___x_2257_, 0);
                    v_a_2271_ = lean_ctor_get(v___x_2257_, 1);
                    v_isSharedCheck_2278_ = (!lean_is_exclusive(v___x_2257_)) as u8;
                    if v_isSharedCheck_2278_ == 0 {
                        v___x_2273_ = v___x_2257_;
                        v_isShared_2274_ = v_isSharedCheck_2278_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2271_);
                        lean_inc(v_a_2270_);
                        lean_dec(v___x_2257_);
                        v___x_2273_ = lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2278_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2255_ == 0 {
                    lean_ctor_set(v___x_2254_, 0, v_a_2258_);
                    v___x_2264_ = v___x_2254_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2258_);
                    v___x_2264_ = v_reuseFailAlloc_2268_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2262_ == 0 {
                    lean_ctor_set(v___x_2261_, 0, v___x_2264_);
                    v___x_2266_ = v___x_2261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_a_2259_);
                    v___x_2266_ = v_reuseFailAlloc_2267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2266_;
            }
            5 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2270_);
                    lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_decodeNameMap___redArg___lam__0(
    mut v_fst_2280_: *mut LeanObject,
    mut v_m_2281_: *mut LeanObject,
    mut v_v_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___x_2283_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_2280_,
        v_v_2282_,
        v_m_2281_,
    );
    return v___x_2283_;
}
pub unsafe fn l_Lake_Toml_Table_decodeNameMap___redArg___lam__1(
    mut v_dec_2284_: *mut LeanObject,
    mut v_x1_2285_: *mut LeanObject,
    mut v_x2_2286_: *mut LeanObject,
    mut v___y_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2288_ = lean_ctor_get(v_x2_2286_, 0);
    lean_inc(v_fst_2288_);
    v_snd_2289_ = lean_ctor_get(v_x2_2286_, 1);
    lean_inc(v_snd_2289_);
    lean_dec_ref(v_x2_2286_);
    v___f_2290_ = lean_alloc_closure(
        l_Lake_Toml_Table_decodeNameMap___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2290_, 0, v_fst_2288_);
    v___x_2291_ = lean_apply_1(v_dec_2284_, v_snd_2289_);
    v___x_2292_ =
        l_Lake_Toml_mergeErrors___redArg(v_x1_2285_, v___x_2291_, v___f_2290_, v___y_2287_);
    return v___x_2292_;
}
pub unsafe fn l_Lake_Toml_Table_decodeNameMap___redArg(
    mut v_dec_2295_: *mut LeanObject,
    mut v_t_2296_: *mut LeanObject,
    mut v_a_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_items_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: usize = 0;
    let mut v___x_150__overap_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_155__overap_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut v_unused_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_items_2298_ = lean_ctor_get(v_t_2296_, 0);
                v_isSharedCheck_2324_ = (!lean_is_exclusive(v_t_2296_)) as u8;
                if v_isSharedCheck_2324_ == 0 {
                    v_unused_2325_ = lean_ctor_get(v_t_2296_, 1);
                    lean_dec(v_unused_2325_);
                    v___x_2300_ = v_t_2296_;
                    v_isShared_2301_ = v_isSharedCheck_2324_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_items_2298_);
                    lean_dec(v_t_2296_);
                    v___x_2300_ = lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2302_ = lean_box(1);
                v___x_2303_ = lean_unsigned_to_nat(0);
                v___x_2304_ = lean_array_get_size(v_items_2298_);
                v___x_2305_ = l_Lake_Toml_decodeArray___redArg___closed__9;
                v___x_2306_ = lean_nat_dec_lt(v___x_2303_, v___x_2304_);
                if v___x_2306_ == 0 {
                    lean_dec_ref(v_items_2298_);
                    lean_dec_ref(v_dec_2295_);
                    if v_isShared_2301_ == 0 {
                        lean_ctor_set(v___x_2300_, 1, v_a_2297_);
                        lean_ctor_set(v___x_2300_, 0, v___x_2302_);
                        v___x_2308_ = v___x_2300_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2302_);
                        lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_a_2297_);
                        v___x_2308_ = v_reuseFailAlloc_2309_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___f_2310_ = lean_alloc_closure(
                        l_Lake_Toml_Table_decodeNameMap___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    lean_closure_set(v___f_2310_, 0, v_dec_2295_);
                    v___x_2311_ = l_Lake_Toml_Table_decodeNameMap___redArg___closed__0;
                    v___x_2312_ = lean_nat_dec_le(v___x_2304_, v___x_2304_);
                    if v___x_2312_ == 0 {
                        if v___x_2306_ == 0 {
                            lean_dec_ref(v___f_2310_);
                            lean_dec_ref(v_items_2298_);
                            if v_isShared_2301_ == 0 {
                                lean_ctor_set(v___x_2300_, 1, v_a_2297_);
                                lean_ctor_set(v___x_2300_, 0, v___x_2302_);
                                v___x_2314_ = v___x_2300_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2302_);
                                lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_a_2297_);
                                v___x_2314_ = v_reuseFailAlloc_2315_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2300_);
                            v___x_2316_ = 0usize;
                            v___x_2317_ = lean_usize_of_nat(v___x_2304_);
                            v___x_150__overap_2318_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2305_,
                                    v___f_2310_,
                                    v_items_2298_,
                                    v___x_2316_,
                                    v___x_2317_,
                                    v___x_2311_,
                                );
                            v___x_2319_ = lean_apply_1(v___x_150__overap_2318_, v_a_2297_);
                            return v___x_2319_;
                        }
                    } else {
                        lean_del_object(v___x_2300_);
                        v___x_2320_ = 0usize;
                        v___x_2321_ = lean_usize_of_nat(v___x_2304_);
                        v___x_155__overap_2322_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_2305_,
                                v___f_2310_,
                                v_items_2298_,
                                v___x_2320_,
                                v___x_2321_,
                                v___x_2311_,
                            );
                        v___x_2323_ = lean_apply_1(v___x_155__overap_2322_, v_a_2297_);
                        return v___x_2323_;
                    }
                }
            }
            2 => {
                return v___x_2308_;
            }
            3 => {
                return v___x_2314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_decodeNameMap(
    mut v_00_u03b1_2326_: *mut LeanObject,
    mut v_dec_2327_: *mut LeanObject,
    mut v_t_2328_: *mut LeanObject,
    mut v_a_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    v___x_2330_ = l_Lake_Toml_Table_decodeNameMap___redArg(v_dec_2327_, v_t_2328_, v_a_2329_);
    return v___x_2330_;
}
pub unsafe fn l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0(
    mut v_inst_2331_: *mut LeanObject,
    mut v_x_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = l_Lake_Toml_Value_decodeTable(v_x_2332_, v___y_2333_);
                if lean_obj_tag(v___x_2334_) == 0 {
                    v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
                    lean_inc(v_a_2335_);
                    v_a_2336_ = lean_ctor_get(v___x_2334_, 1);
                    lean_inc(v_a_2336_);
                    lean_dec_ref_known(v___x_2334_, 2);
                    v___x_2337_ = l_Lake_Toml_Table_decodeNameMap___redArg(
                        v_inst_2331_,
                        v_a_2335_,
                        v_a_2336_,
                    );
                    return v___x_2337_;
                } else {
                    lean_dec_ref(v_inst_2331_);
                    v_a_2338_ = lean_ctor_get(v___x_2334_, 0);
                    v_a_2339_ = lean_ctor_get(v___x_2334_, 1);
                    v_isSharedCheck_2346_ = (!lean_is_exclusive(v___x_2334_)) as u8;
                    if v_isSharedCheck_2346_ == 0 {
                        v___x_2341_ = v___x_2334_;
                        v_isShared_2342_ = v_isSharedCheck_2346_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2339_);
                        lean_inc(v_a_2338_);
                        lean_dec(v___x_2334_);
                        v___x_2341_ = lean_box(0);
                        v_isShared_2342_ = v_isSharedCheck_2346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2342_ == 0 {
                    v___x_2344_ = v___x_2341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2338_);
                    lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_a_2339_);
                    v___x_2344_ = v_reuseFailAlloc_2345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_instDecodeTomlNameMap___redArg(
    mut v_inst_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2348_: *mut LeanObject = core::ptr::null_mut();
    v___f_2348_ = lean_alloc_closure(
        l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2348_, 0, v_inst_2347_);
    return v___f_2348_;
}
pub unsafe fn l_Lake_Toml_Table_instDecodeTomlNameMap(
    mut v_00_u03b1_2349_: *mut LeanObject,
    mut v_inst_2350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2351_: *mut LeanObject = core::ptr::null_mut();
    v___f_2351_ = lean_alloc_closure(
        l_Lake_Toml_Table_instDecodeTomlNameMap___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2351_, 0, v_inst_2350_);
    return v___f_2351_;
}
pub unsafe fn l_Lake_Toml_Table_tryDecode___redArg(
    mut v_inst_2352_: *mut LeanObject,
    mut v_dec_2353_: *mut LeanObject,
    mut v_t_2354_: *mut LeanObject,
    mut v_k_2355_: *mut LeanObject,
    mut v_ref_2356_: *mut LeanObject,
    mut v_a_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v_a_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_unused_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_unused_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_k_2355_);
                v___x_2358_ =
                    l_Lake_Toml_Table_decodeValue(v_t_2354_, v_k_2355_, v_ref_2356_, v_a_2357_);
                if lean_obj_tag(v___x_2358_) == 0 {
                    v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
                    lean_inc(v_a_2359_);
                    v_a_2360_ = lean_ctor_get(v___x_2358_, 1);
                    lean_inc(v_a_2360_);
                    lean_dec_ref_known(v___x_2358_, 2);
                    v___x_2361_ = l_Lake_Toml_decodeKeyval___redArg(
                        v_dec_2353_,
                        v_k_2355_,
                        v_a_2359_,
                        v_a_2360_,
                    );
                    if lean_obj_tag(v___x_2361_) == 0 {
                        lean_dec(v_inst_2352_);
                        v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
                        v_a_2363_ = lean_ctor_get(v___x_2361_, 1);
                        v_isSharedCheck_2370_ = (!lean_is_exclusive(v___x_2361_)) as u8;
                        if v_isSharedCheck_2370_ == 0 {
                            v___x_2365_ = v___x_2361_;
                            v_isShared_2366_ = v_isSharedCheck_2370_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2363_);
                            lean_inc(v_a_2362_);
                            lean_dec(v___x_2361_);
                            v___x_2365_ = lean_box(0);
                            v_isShared_2366_ = v_isSharedCheck_2370_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2371_ = lean_ctor_get(v___x_2361_, 1);
                        v_isSharedCheck_2378_ = (!lean_is_exclusive(v___x_2361_)) as u8;
                        if v_isSharedCheck_2378_ == 0 {
                            v_unused_2379_ = lean_ctor_get(v___x_2361_, 0);
                            lean_dec(v_unused_2379_);
                            v___x_2373_ = v___x_2361_;
                            v_isShared_2374_ = v_isSharedCheck_2378_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2371_);
                            lean_dec(v___x_2361_);
                            v___x_2373_ = lean_box(0);
                            v_isShared_2374_ = v_isSharedCheck_2378_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_2355_);
                    lean_dec_ref(v_dec_2353_);
                    v_a_2380_ = lean_ctor_get(v___x_2358_, 1);
                    v_isSharedCheck_2387_ = (!lean_is_exclusive(v___x_2358_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v_unused_2388_ = lean_ctor_get(v___x_2358_, 0);
                        lean_dec(v_unused_2388_);
                        v___x_2382_ = v___x_2358_;
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2380_);
                        lean_dec(v___x_2358_);
                        v___x_2382_ = lean_box(0);
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2366_ == 0 {
                    v___x_2368_ = v___x_2365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2362_);
                    lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_a_2363_);
                    v___x_2368_ = v_reuseFailAlloc_2369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2368_;
            }
            3 => {
                if v_isShared_2374_ == 0 {
                    lean_ctor_set_tag(v___x_2373_, 0);
                    lean_ctor_set(v___x_2373_, 0, v_inst_2352_);
                    v___x_2376_ = v___x_2373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_inst_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_a_2371_);
                    v___x_2376_ = v_reuseFailAlloc_2377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2376_;
            }
            5 => {
                if v_isShared_2383_ == 0 {
                    lean_ctor_set_tag(v___x_2382_, 0);
                    lean_ctor_set(v___x_2382_, 0, v_inst_2352_);
                    v___x_2385_ = v___x_2382_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_inst_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_a_2380_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_tryDecode(
    mut v_00_u03b1_2389_: *mut LeanObject,
    mut v_inst_2390_: *mut LeanObject,
    mut v_dec_2391_: *mut LeanObject,
    mut v_t_2392_: *mut LeanObject,
    mut v_k_2393_: *mut LeanObject,
    mut v_ref_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2404_: u8 = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut v_a_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_unused_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut v_unused_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_k_2393_);
                v___x_2396_ =
                    l_Lake_Toml_Table_decodeValue(v_t_2392_, v_k_2393_, v_ref_2394_, v_a_2395_);
                if lean_obj_tag(v___x_2396_) == 0 {
                    v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
                    lean_inc(v_a_2397_);
                    v_a_2398_ = lean_ctor_get(v___x_2396_, 1);
                    lean_inc(v_a_2398_);
                    lean_dec_ref_known(v___x_2396_, 2);
                    v___x_2399_ = l_Lake_Toml_decodeKeyval___redArg(
                        v_dec_2391_,
                        v_k_2393_,
                        v_a_2397_,
                        v_a_2398_,
                    );
                    if lean_obj_tag(v___x_2399_) == 0 {
                        lean_dec(v_inst_2390_);
                        v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
                        v_a_2401_ = lean_ctor_get(v___x_2399_, 1);
                        v_isSharedCheck_2408_ = (!lean_is_exclusive(v___x_2399_)) as u8;
                        if v_isSharedCheck_2408_ == 0 {
                            v___x_2403_ = v___x_2399_;
                            v_isShared_2404_ = v_isSharedCheck_2408_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2401_);
                            lean_inc(v_a_2400_);
                            lean_dec(v___x_2399_);
                            v___x_2403_ = lean_box(0);
                            v_isShared_2404_ = v_isSharedCheck_2408_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2409_ = lean_ctor_get(v___x_2399_, 1);
                        v_isSharedCheck_2416_ = (!lean_is_exclusive(v___x_2399_)) as u8;
                        if v_isSharedCheck_2416_ == 0 {
                            v_unused_2417_ = lean_ctor_get(v___x_2399_, 0);
                            lean_dec(v_unused_2417_);
                            v___x_2411_ = v___x_2399_;
                            v_isShared_2412_ = v_isSharedCheck_2416_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2409_);
                            lean_dec(v___x_2399_);
                            v___x_2411_ = lean_box(0);
                            v_isShared_2412_ = v_isSharedCheck_2416_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_2393_);
                    lean_dec_ref(v_dec_2391_);
                    v_a_2418_ = lean_ctor_get(v___x_2396_, 1);
                    v_isSharedCheck_2425_ = (!lean_is_exclusive(v___x_2396_)) as u8;
                    if v_isSharedCheck_2425_ == 0 {
                        v_unused_2426_ = lean_ctor_get(v___x_2396_, 0);
                        lean_dec(v_unused_2426_);
                        v___x_2420_ = v___x_2396_;
                        v_isShared_2421_ = v_isSharedCheck_2425_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2418_);
                        lean_dec(v___x_2396_);
                        v___x_2420_ = lean_box(0);
                        v_isShared_2421_ = v_isSharedCheck_2425_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2404_ == 0 {
                    v___x_2406_ = v___x_2403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2400_);
                    lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_a_2401_);
                    v___x_2406_ = v_reuseFailAlloc_2407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2406_;
            }
            3 => {
                if v_isShared_2412_ == 0 {
                    lean_ctor_set_tag(v___x_2411_, 0);
                    lean_ctor_set(v___x_2411_, 0, v_inst_2390_);
                    v___x_2414_ = v___x_2411_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_inst_2390_);
                    lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_a_2409_);
                    v___x_2414_ = v_reuseFailAlloc_2415_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2414_;
            }
            5 => {
                if v_isShared_2421_ == 0 {
                    lean_ctor_set_tag(v___x_2420_, 0);
                    lean_ctor_set(v___x_2420_, 0, v_inst_2390_);
                    v___x_2423_ = v___x_2420_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_inst_2390_);
                    lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_a_2418_);
                    v___x_2423_ = v_reuseFailAlloc_2424_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_tryDecode_x3f___redArg(
    mut v_dec_2427_: *mut LeanObject,
    mut v_t_2428_: *mut LeanObject,
    mut v_k_2429_: *mut LeanObject,
    mut v_a_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v_snd_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_a_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2461_: u8 = 0;
    let mut v_unused_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2431_ = l_Lake_Toml_Table_decodeValue___closed__0;
                v___x_2432_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2431_, v_k_2429_, v_t_2428_);
                if lean_obj_tag(v___x_2432_) == 0 {
                    lean_dec_ref(v_dec_2427_);
                    v___x_2433_ = lean_box(0);
                    v___x_2434_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2434_, 0, v___x_2433_);
                    lean_ctor_set(v___x_2434_, 1, v_a_2430_);
                    return v___x_2434_;
                } else {
                    v_val_2435_ = lean_ctor_get(v___x_2432_, 0);
                    v_isSharedCheck_2463_ = (!lean_is_exclusive(v___x_2432_)) as u8;
                    if v_isSharedCheck_2463_ == 0 {
                        v___x_2437_ = v___x_2432_;
                        v_isShared_2438_ = v_isSharedCheck_2463_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2435_);
                        lean_dec(v___x_2432_);
                        v___x_2437_ = lean_box(0);
                        v_isShared_2438_ = v_isSharedCheck_2463_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2439_ = lean_ctor_get(v_val_2435_, 1);
                lean_inc(v_snd_2439_);
                lean_dec(v_val_2435_);
                v___x_2440_ = lean_apply_2(v_dec_2427_, v_snd_2439_, v_a_2430_);
                if lean_obj_tag(v___x_2440_) == 0 {
                    v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
                    v_a_2442_ = lean_ctor_get(v___x_2440_, 1);
                    v_isSharedCheck_2452_ = (!lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2452_ == 0 {
                        v___x_2444_ = v___x_2440_;
                        v_isShared_2445_ = v_isSharedCheck_2452_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2442_);
                        lean_inc(v_a_2441_);
                        lean_dec(v___x_2440_);
                        v___x_2444_ = lean_box(0);
                        v_isShared_2445_ = v_isSharedCheck_2452_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2437_);
                    v_a_2453_ = lean_ctor_get(v___x_2440_, 1);
                    v_isSharedCheck_2461_ = (!lean_is_exclusive(v___x_2440_)) as u8;
                    if v_isSharedCheck_2461_ == 0 {
                        v_unused_2462_ = lean_ctor_get(v___x_2440_, 0);
                        lean_dec(v_unused_2462_);
                        v___x_2455_ = v___x_2440_;
                        v_isShared_2456_ = v_isSharedCheck_2461_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2453_);
                        lean_dec(v___x_2440_);
                        v___x_2455_ = lean_box(0);
                        v_isShared_2456_ = v_isSharedCheck_2461_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2438_ == 0 {
                    lean_ctor_set(v___x_2437_, 0, v_a_2441_);
                    v___x_2447_ = v___x_2437_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2441_);
                    v___x_2447_ = v_reuseFailAlloc_2451_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2445_ == 0 {
                    lean_ctor_set(v___x_2444_, 0, v___x_2447_);
                    v___x_2449_ = v___x_2444_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
                    lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_a_2442_);
                    v___x_2449_ = v_reuseFailAlloc_2450_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2449_;
            }
            5 => {
                v___x_2457_ = lean_box(0);
                if v_isShared_2456_ == 0 {
                    lean_ctor_set_tag(v___x_2455_, 0);
                    lean_ctor_set(v___x_2455_, 0, v___x_2457_);
                    v___x_2459_ = v___x_2455_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
                    lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_a_2453_);
                    v___x_2459_ = v_reuseFailAlloc_2460_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_tryDecode_x3f(
    mut v_00_u03b1_2464_: *mut LeanObject,
    mut v_dec_2465_: *mut LeanObject,
    mut v_t_2466_: *mut LeanObject,
    mut v_k_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v_snd_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v_a_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2499_: u8 = 0;
    let mut v_unused_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2469_ = l_Lake_Toml_Table_decodeValue___closed__0;
                v___x_2470_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2469_, v_k_2467_, v_t_2466_);
                if lean_obj_tag(v___x_2470_) == 0 {
                    lean_dec_ref(v_dec_2465_);
                    v___x_2471_ = lean_box(0);
                    v___x_2472_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2472_, 0, v___x_2471_);
                    lean_ctor_set(v___x_2472_, 1, v_a_2468_);
                    return v___x_2472_;
                } else {
                    v_val_2473_ = lean_ctor_get(v___x_2470_, 0);
                    v_isSharedCheck_2501_ = (!lean_is_exclusive(v___x_2470_)) as u8;
                    if v_isSharedCheck_2501_ == 0 {
                        v___x_2475_ = v___x_2470_;
                        v_isShared_2476_ = v_isSharedCheck_2501_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2473_);
                        lean_dec(v___x_2470_);
                        v___x_2475_ = lean_box(0);
                        v_isShared_2476_ = v_isSharedCheck_2501_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2477_ = lean_ctor_get(v_val_2473_, 1);
                lean_inc(v_snd_2477_);
                lean_dec(v_val_2473_);
                v___x_2478_ = lean_apply_2(v_dec_2465_, v_snd_2477_, v_a_2468_);
                if lean_obj_tag(v___x_2478_) == 0 {
                    v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
                    v_a_2480_ = lean_ctor_get(v___x_2478_, 1);
                    v_isSharedCheck_2490_ = (!lean_is_exclusive(v___x_2478_)) as u8;
                    if v_isSharedCheck_2490_ == 0 {
                        v___x_2482_ = v___x_2478_;
                        v_isShared_2483_ = v_isSharedCheck_2490_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2480_);
                        lean_inc(v_a_2479_);
                        lean_dec(v___x_2478_);
                        v___x_2482_ = lean_box(0);
                        v_isShared_2483_ = v_isSharedCheck_2490_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2475_);
                    v_a_2491_ = lean_ctor_get(v___x_2478_, 1);
                    v_isSharedCheck_2499_ = (!lean_is_exclusive(v___x_2478_)) as u8;
                    if v_isSharedCheck_2499_ == 0 {
                        v_unused_2500_ = lean_ctor_get(v___x_2478_, 0);
                        lean_dec(v_unused_2500_);
                        v___x_2493_ = v___x_2478_;
                        v_isShared_2494_ = v_isSharedCheck_2499_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2491_);
                        lean_dec(v___x_2478_);
                        v___x_2493_ = lean_box(0);
                        v_isShared_2494_ = v_isSharedCheck_2499_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2476_ == 0 {
                    lean_ctor_set(v___x_2475_, 0, v_a_2479_);
                    v___x_2485_ = v___x_2475_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2479_);
                    v___x_2485_ = v_reuseFailAlloc_2489_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2483_ == 0 {
                    lean_ctor_set(v___x_2482_, 0, v___x_2485_);
                    v___x_2487_ = v___x_2482_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
                    lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_a_2480_);
                    v___x_2487_ = v_reuseFailAlloc_2488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2487_;
            }
            5 => {
                v___x_2495_ = lean_box(0);
                if v_isShared_2494_ == 0 {
                    lean_ctor_set_tag(v___x_2493_, 0);
                    lean_ctor_set(v___x_2493_, 0, v___x_2495_);
                    v___x_2497_ = v___x_2493_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
                    lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_a_2491_);
                    v___x_2497_ = v_reuseFailAlloc_2498_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2497_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_tryDecodeD___redArg(
    mut v_dec_2502_: *mut LeanObject,
    mut v_k_2503_: *mut LeanObject,
    mut v_default_2504_: *mut LeanObject,
    mut v_t_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_a_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_unused_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2507_ = l_Lake_Toml_Table_decodeValue___closed__0;
                v___x_2508_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2507_, v_k_2503_, v_t_2505_);
                if lean_obj_tag(v___x_2508_) == 0 {
                    lean_dec_ref(v_dec_2502_);
                    v___x_2509_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2509_, 0, v_default_2504_);
                    lean_ctor_set(v___x_2509_, 1, v_a_2506_);
                    return v___x_2509_;
                } else {
                    v_val_2510_ = lean_ctor_get(v___x_2508_, 0);
                    lean_inc(v_val_2510_);
                    lean_dec_ref_known(v___x_2508_, 1);
                    v_snd_2511_ = lean_ctor_get(v_val_2510_, 1);
                    lean_inc(v_snd_2511_);
                    lean_dec(v_val_2510_);
                    v___x_2512_ = lean_apply_2(v_dec_2502_, v_snd_2511_, v_a_2506_);
                    if lean_obj_tag(v___x_2512_) == 0 {
                        lean_dec(v_default_2504_);
                        v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
                        v_a_2514_ = lean_ctor_get(v___x_2512_, 1);
                        v_isSharedCheck_2521_ = (!lean_is_exclusive(v___x_2512_)) as u8;
                        if v_isSharedCheck_2521_ == 0 {
                            v___x_2516_ = v___x_2512_;
                            v_isShared_2517_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2514_);
                            lean_inc(v_a_2513_);
                            lean_dec(v___x_2512_);
                            v___x_2516_ = lean_box(0);
                            v_isShared_2517_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2522_ = lean_ctor_get(v___x_2512_, 1);
                        v_isSharedCheck_2529_ = (!lean_is_exclusive(v___x_2512_)) as u8;
                        if v_isSharedCheck_2529_ == 0 {
                            v_unused_2530_ = lean_ctor_get(v___x_2512_, 0);
                            lean_dec(v_unused_2530_);
                            v___x_2524_ = v___x_2512_;
                            v_isShared_2525_ = v_isSharedCheck_2529_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2522_);
                            lean_dec(v___x_2512_);
                            v___x_2524_ = lean_box(0);
                            v_isShared_2525_ = v_isSharedCheck_2529_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2517_ == 0 {
                    v___x_2519_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2513_);
                    lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_a_2514_);
                    v___x_2519_ = v_reuseFailAlloc_2520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2519_;
            }
            3 => {
                if v_isShared_2525_ == 0 {
                    lean_ctor_set_tag(v___x_2524_, 0);
                    lean_ctor_set(v___x_2524_, 0, v_default_2504_);
                    v___x_2527_ = v___x_2524_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_default_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_a_2522_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_Table_tryDecodeD(
    mut v_00_u03b1_2531_: *mut LeanObject,
    mut v_dec_2532_: *mut LeanObject,
    mut v_k_2533_: *mut LeanObject,
    mut v_default_2534_: *mut LeanObject,
    mut v_t_2535_: *mut LeanObject,
    mut v_a_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut v_a_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_unused_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2537_ = l_Lake_Toml_Table_decodeValue___closed__0;
                v___x_2538_ =
                    l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_2537_, v_k_2533_, v_t_2535_);
                if lean_obj_tag(v___x_2538_) == 0 {
                    lean_dec_ref(v_dec_2532_);
                    v___x_2539_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2539_, 0, v_default_2534_);
                    lean_ctor_set(v___x_2539_, 1, v_a_2536_);
                    return v___x_2539_;
                } else {
                    v_val_2540_ = lean_ctor_get(v___x_2538_, 0);
                    lean_inc(v_val_2540_);
                    lean_dec_ref_known(v___x_2538_, 1);
                    v_snd_2541_ = lean_ctor_get(v_val_2540_, 1);
                    lean_inc(v_snd_2541_);
                    lean_dec(v_val_2540_);
                    v___x_2542_ = lean_apply_2(v_dec_2532_, v_snd_2541_, v_a_2536_);
                    if lean_obj_tag(v___x_2542_) == 0 {
                        lean_dec(v_default_2534_);
                        v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
                        v_a_2544_ = lean_ctor_get(v___x_2542_, 1);
                        v_isSharedCheck_2551_ = (!lean_is_exclusive(v___x_2542_)) as u8;
                        if v_isSharedCheck_2551_ == 0 {
                            v___x_2546_ = v___x_2542_;
                            v_isShared_2547_ = v_isSharedCheck_2551_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2544_);
                            lean_inc(v_a_2543_);
                            lean_dec(v___x_2542_);
                            v___x_2546_ = lean_box(0);
                            v_isShared_2547_ = v_isSharedCheck_2551_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2552_ = lean_ctor_get(v___x_2542_, 1);
                        v_isSharedCheck_2559_ = (!lean_is_exclusive(v___x_2542_)) as u8;
                        if v_isSharedCheck_2559_ == 0 {
                            v_unused_2560_ = lean_ctor_get(v___x_2542_, 0);
                            lean_dec(v_unused_2560_);
                            v___x_2554_ = v___x_2542_;
                            v_isShared_2555_ = v_isSharedCheck_2559_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2552_);
                            lean_dec(v___x_2542_);
                            v___x_2554_ = lean_box(0);
                            v_isShared_2555_ = v_isSharedCheck_2559_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2547_ == 0 {
                    v___x_2549_ = v___x_2546_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2543_);
                    lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_a_2544_);
                    v___x_2549_ = v_reuseFailAlloc_2550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2549_;
            }
            3 => {
                if v_isShared_2555_ == 0 {
                    lean_ctor_set_tag(v___x_2554_, 0);
                    lean_ctor_set(v___x_2554_, 0, v_default_2534_);
                    v___x_2557_ = v___x_2554_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_default_2534_);
                    lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_a_2552_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2557_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Decode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Decode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Decode(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Toml_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Decode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Decode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Decode(builtin);
}
