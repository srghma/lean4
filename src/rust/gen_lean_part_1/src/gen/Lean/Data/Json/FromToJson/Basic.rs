// Lean compiler output
// Module: Lean.Data.Json.FromToJson.Basic
// Imports: Lean.Data.Json.Printer Init.Data.ToString.Macro Init.Data.Array.GetLit
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_float_div,
    lean_float_negate, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_pow, lean_string_append, lean_string_dec_eq, lean_string_utf8_extract,
    lean_uint64_of_nat, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Except::{
    l_Except_bind, l_Except_instMonad___lam__0, l_Except_instMonad___lam__1,
    l_Except_instMonad___lam__2___boxed, l_Except_instMonad___lam__3, l_Except_map, l_Except_pure,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Array::GetLit::{
    initialize_Init_Data_Array_GetLit, runtime_initialize_Init_Data_Array_GetLit,
};
use crate::r#gen::Init::Data::OfScientific::l_Float_ofScientific;
use crate::r#gen::Init::Data::Ord::String::l_String_compare___boxed;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_toSlice;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_decodeNatLitVal_x3f, l_String_toName};
use crate::r#gen::Init::Prelude::{l_Function_comp, l_System_Platform_numBits, l_id___boxed};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getArr_x3f, l_Lean_Json_getBool_x3f___boxed, l_Lean_Json_getInt_x3f,
    l_Lean_Json_getNat_x3f, l_Lean_Json_getNum_x3f, l_Lean_Json_getObjVal_x3f,
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_setObjVal_x21,
    l_Lean_JsonNumber_fromFloat_x3f, l_Lean_JsonNumber_fromInt, l_Lean_JsonNumber_fromNat,
    l_Lean_JsonNumber_toFloat,
};
use crate::r#gen::Lean::Data::Json::Printer::{
    initialize_Lean_Data_Json_Printer, l_Lean_Json_pretty,
    runtime_initialize_Lean_Data_Json_Printer,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getString_x21, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert_x21___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_foldl___redArg, l_Std_DTreeMap_Internal_Impl_foldlM___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg,
};
pub static l_Lean_instFromJsonJson___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJson___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJson___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonJson___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_instToJsonJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJson___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJson___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonJsonNumber___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getNum_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonJsonNumber___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJsonNumber___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonJsonNumber: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJsonNumber___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonJsonNumber___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonJsonNumber___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonJsonNumber___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJsonNumber___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonJsonNumber: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJsonNumber___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonUnit___lam__0___closed__0_value: leanh::LeanStringObject<33> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 123, 125, 32, 116, 111, 32, 100, 101, 99,
            111, 100, 101, 32, 85, 110, 105, 116, 44, 32, 103, 111, 116, 32, 0,
        ],
    };
static mut l_Lean_instFromJsonUnit___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonUnit___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_instFromJsonUnit___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonUnit___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonUnit___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonUnit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonUnit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonUnit___lam__0___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_instToJsonUnit___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUnit___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonUnit___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonUnit___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonUnit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUnit___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonUnit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUnit___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonEmpty___lam__0___closed__0_value: leanh::LeanStringObject<52> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            116, 121, 112, 101, 32, 69, 109, 112, 116, 121, 32, 104, 97, 115, 32, 110, 111, 32, 99,
            111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 111, 32, 109, 97, 116, 99,
            104, 32, 74, 83, 79, 78, 32, 118, 97, 108, 117, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_instFromJsonEmpty___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonEmpty___lam__0___closed__1_value: leanh::LeanStringObject<
    122,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 122,
    m_capacity: 122,
    m_length: 121,
    m_data: [
        39, 46, 32, 84, 104, 105, 115, 32, 111, 99, 99, 117, 114, 115, 32, 119, 104, 101, 110, 32,
        100, 101, 115, 101, 114, 105, 97, 108, 105, 122, 105, 110, 103, 32, 97, 32, 118, 97, 108,
        117, 101, 32, 102, 111, 114, 32, 116, 121, 112, 101, 32, 69, 109, 112, 116, 121, 44, 32,
        101, 46, 103, 46, 32, 97, 116, 32, 116, 121, 112, 101, 32, 79, 112, 116, 105, 111, 110, 32,
        69, 109, 112, 116, 121, 32, 119, 105, 116, 104, 32, 99, 111, 100, 101, 32, 102, 111, 114,
        32, 116, 104, 101, 32, 39, 115, 111, 109, 101, 39, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 46, 0,
    ],
};
static mut l_Lean_instFromJsonEmpty___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonEmpty___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonEmpty___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonEmpty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonEmpty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonEmpty___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonEmpty___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonEmpty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonEmpty___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonEmpty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonEmpty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonBool___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getBool_x3f___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonBool___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonBool: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonBool___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonBool___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonBool___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonBool: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonBool___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getNat_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonNat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonInt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getInt_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonInt___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonInt___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonInt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonInt___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonInt___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonInt___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonString___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonString___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_toSlice as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonSlice___closed__1_value: leanh::LeanClosureObject<4> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_map as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instFromJsonSlice___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonSlice___closed__2_value: leanh::LeanClosureObject<5> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_comp as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonString___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instFromJsonSlice___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonSlice: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonSlice___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonSlice___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonSlice: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonSlice___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonFilePath___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonFilePath___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonFilePath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFilePath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__4_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Except_map as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Array_fromJson_x3f___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__5_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_fromJson_x3f___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__6_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Except_pure as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Array_fromJson_x3f___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__7_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_fromJson_x3f___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__8_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Except_bind as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Array_fromJson_x3f___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_fromJson_x3f___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__10_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121,
            44, 32, 103, 111, 116, 32, 39, 0,
        ],
    };
static mut l_Array_fromJson_x3f___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__11_value: leanh::LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Array_fromJson_x3f___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_toJson___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_toJson___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_toJson___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_toJson___redArg___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_toJson___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_toJson___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___redArg___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Option_fromJson_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_fromJson_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Prod_fromJson_x3f___redArg___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 112, 97, 105, 114, 44, 32, 103, 111, 116,
            32, 39, 0,
        ],
    };
static mut l_Prod_fromJson_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_fromJson_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_fromJson_x3f___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
    };
static mut l_Lean_Name_fromJson_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_fromJson_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_fromJson_x3f___closed__1_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32,
            103, 111, 116, 32, 39, 0,
        ],
    };
static mut l_Lean_Name_fromJson_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_fromJson_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_fromJson_x3f___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Name_fromJson_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_fromJson_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonName___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonName___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonName: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonName___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonName___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonName___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonName___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonName: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonName___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value: leanh::LeanStringObject<
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112, 96,
        44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l_Lean_NameMap_fromJson_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_NameMap_toJson___redArg___lam__0___closed__0_value:
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
    m_fun: l_String_compare___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_NameMap_toJson___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_toJson___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_bignumFromJson_x3f___closed__0_value: leanh::LeanStringObject<40> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 116, 114, 105, 110, 103, 45,
            101, 110, 99, 111, 100, 101, 100, 32, 110, 117, 109, 98, 101, 114, 44, 32, 103, 111,
            116, 32, 39, 0,
        ],
    };
static mut l_Lean_bignumFromJson_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_bignumFromJson_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_USize_fromJson_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_USize_fromJson_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_USize_fromJson_x3f___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [118, 97, 108, 117, 101, 32, 39, 0],
    };
static mut l_USize_fromJson_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_USize_fromJson_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l_USize_fromJson_x3f___closed__2_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
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
            39, 32, 105, 115, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 102, 111, 114, 32,
            96, 85, 83, 105, 122, 101, 96, 0,
        ],
    };
static mut l_USize_fromJson_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_USize_fromJson_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonUSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_USize_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonUSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUSize___closed__0_value) as *mut leanh::LeanObject;
static mut l_UInt64_fromJson_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_UInt64_fromJson_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_UInt64_fromJson_x3f___closed__1_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
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
            39, 32, 105, 115, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 102, 111, 114, 32,
            96, 85, 73, 110, 116, 54, 52, 96, 0,
        ],
    };
static mut l_UInt64_fromJson_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_UInt64_fromJson_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonUInt64___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUInt64___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUInt64___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToJsonUInt64___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToJsonFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFloat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instToJsonFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFloat___closed__0_value) as *mut leanh::LeanObject;
pub static l_Float_fromJson_x3f___closed__0_value: leanh::LeanStringObject<62> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 110, 117, 109, 98, 101, 114, 32, 111,
            114, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 39, 73, 110, 102, 105, 110, 105,
            116, 121, 39, 44, 32, 39, 45, 73, 110, 102, 105, 110, 105, 116, 121, 39, 44, 32, 39,
            78, 97, 78, 39, 46, 0,
        ],
    };
static mut l_Float_fromJson_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l_Float_fromJson_x3f___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Float_fromJson_x3f___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Float_fromJson_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l_Float_fromJson_x3f___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [73, 110, 102, 105, 110, 105, 116, 121, 0],
    };
static mut l_Float_fromJson_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l_Float_fromJson_x3f___closed__3_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [45, 73, 110, 102, 105, 110, 105, 116, 121, 0],
    };
static mut l_Float_fromJson_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__3_value) as *mut leanh::LeanObject;
pub static l_Float_fromJson_x3f___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 78, 0],
    };
static mut l_Float_fromJson_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_instFromJsonFloat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonFloat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFloat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instFromJsonFloat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFloat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_Structured_fromJson_x3f___closed__0_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 100,
        32, 111, 98, 106, 101, 99, 116, 44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l_Lean_Json_Structured_fromJson_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Structured_fromJson_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_instFromJsonStructured___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Json_Structured_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instFromJsonStructured___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instFromJsonStructured___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Json_instFromJsonStructured: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instFromJsonStructured___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_instToJsonStructured___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_Structured_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instToJsonStructured___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToJsonStructured___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Json_instToJsonStructured: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToJsonStructured___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_parseTagged___closed__0_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
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
            105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111,
            102, 32, 102, 105, 101, 108, 100, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Json_parseTagged___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_parseTagged___closed__1_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 3,
        m_data: [32, 226, 137, 159, 32, 0],
    };
static mut l_Lean_Json_parseTagged___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_parseTagged___closed__2_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Json_parseTagged___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_parseTagged___closed__3_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 116, 97, 103, 58, 32, 0,
        ],
    };
static mut l_Lean_Json_parseTagged___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_parseTagged___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_parseTagged___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__4_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instFromJsonJson___lam__0(
    mut v_a_1054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1055_, 0, v_a_1054_);
    return v___x_1055_;
}
pub unsafe fn l_Lean_instToJsonJsonNumber___lam__0(
    mut v_n_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1063_, 0, v_n_1062_);
    return v___x_1063_;
}
pub unsafe fn l_Lean_instFromJsonUnit___lam__0(
    mut v_x_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1069_) == 5 {
                    v_kvPairs_1076_ = leanh::lean_ctor_get(v_x_1069_, 0);
                    if leanh::lean_obj_tag(v_kvPairs_1076_) == 1 {
                        leanh::lean_dec_ref_known(v_x_1069_, 1);
                        v___x_1077_ = l_Lean_instFromJsonUnit___lam__0___closed__1;
                        return v___x_1077_;
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
                v___x_1071_ = l_Lean_instFromJsonUnit___lam__0___closed__0;
                v___x_1072_ = leanh::lean_unsigned_to_nat(80);
                v___x_1073_ = l_Lean_Json_pretty(v_x_1069_, v___x_1072_);
                v___x_1074_ = lean_string_append(v___x_1071_, v___x_1073_);
                leanh::lean_dec_ref(v___x_1073_);
                v___x_1075_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
                return v___x_1075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonUnit___lam__0(
    mut v_x_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_instToJsonUnit___lam__0___closed__0;
    return v___x_1083_;
}
pub unsafe fn l_Lean_instFromJsonEmpty___lam__0(
    mut v_j_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_instFromJsonEmpty___lam__0___closed__0;
    v___x_1090_ = leanh::lean_unsigned_to_nat(80);
    v___x_1091_ = l_Lean_Json_pretty(v_j_1088_, v___x_1090_);
    v___x_1092_ = lean_string_append(v___x_1089_, v___x_1091_);
    leanh::lean_dec_ref(v___x_1091_);
    v___x_1093_ = l_Lean_instFromJsonEmpty___lam__0___closed__1;
    v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
    v___x_1095_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l_Lean_instToJsonEmpty___lam__0(mut v_a_1098_: u8) -> *mut leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_instToJsonEmpty___lam__0___boxed(
    mut v_a_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6__boxed_1100_: u8 = 0;
    let mut v_res_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_6__boxed_1100_ = (leanh::lean_unbox(v_a_1099_) as u8);
    v_res_1101_ = l_Lean_instToJsonEmpty___lam__0(v_a_6__boxed_1100_);
    return v_res_1101_;
}
pub unsafe fn l_Lean_instToJsonBool___lam__0(mut v_b_1106_: u8) -> *mut leanh::LeanObject {
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_1107_, 0 as u32, v_b_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_instToJsonBool___lam__0___boxed(
    mut v_b_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1109_: u8 = 0;
    let mut v_res_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1109_ = (leanh::lean_unbox(v_b_1108_) as u8);
    v_res_1110_ = l_Lean_instToJsonBool___lam__0(v_b_boxed_1109_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_instToJsonNat___lam__0(
    mut v_n_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1116_ = l_Lean_JsonNumber_fromNat(v_n_1115_);
    v___x_1117_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1117_, 0, v___x_1116_);
    return v___x_1117_;
}
pub unsafe fn l_Lean_instToJsonInt___lam__0(
    mut v_n_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_JsonNumber_fromInt(v_n_1122_);
    v___x_1124_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1124_, 0, v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn l_Lean_instToJsonString___lam__0(
    mut v_s_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1130_, 0, v_s_1129_);
    return v___x_1130_;
}
pub unsafe fn l_Lean_instToJsonSlice___lam__0(
    mut v_s_1140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_str_1141_ = leanh::lean_ctor_get(v_s_1140_, 0);
    v_startInclusive_1142_ = leanh::lean_ctor_get(v_s_1140_, 1);
    v_endExclusive_1143_ = leanh::lean_ctor_get(v_s_1140_, 2);
    v___x_1144_ =
        lean_string_utf8_extract(v_str_1141_, v_startInclusive_1142_, v_endExclusive_1143_);
    v___x_1145_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1145_, 0, v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_instToJsonSlice___lam__0___boxed(
    mut v_s_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1147_ = l_Lean_instToJsonSlice___lam__0(v_s_1146_);
    leanh::lean_dec_ref(v_s_1146_);
    return v_res_1147_;
}
pub unsafe fn l_Lean_instFromJsonFilePath___lam__0(
    mut v_j_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_a_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1151_ = l_Lean_Json_getStr_x3f(v_j_1150_);
                if leanh::lean_obj_tag(v___x_1151_) == 0 {
                    v_a_1152_ = leanh::lean_ctor_get(v___x_1151_, 0);
                    v_isSharedCheck_1159_ = (!leanh::lean_is_exclusive(v___x_1151_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v___x_1154_ = v___x_1151_;
                        v_isShared_1155_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1152_);
                        leanh::lean_dec(v___x_1151_);
                        v___x_1154_ = leanh::lean_box(0);
                        v_isShared_1155_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1160_ = leanh::lean_ctor_get(v___x_1151_, 0);
                    v_isSharedCheck_1167_ = (!leanh::lean_is_exclusive(v___x_1151_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1162_ = v___x_1151_;
                        v_isShared_1163_ = v_isSharedCheck_1167_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1160_);
                        leanh::lean_dec(v___x_1151_);
                        v___x_1162_ = leanh::lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1167_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1155_ == 0 {
                    v___x_1157_ = v___x_1154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
                    v___x_1157_ = v_reuseFailAlloc_1158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1157_;
            }
            3 => {
                if v_isShared_1163_ == 0 {
                    v___x_1165_ = v___x_1162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonFilePath___lam__0(
    mut v_p_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1171_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1171_, 0, v_p_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Array_fromJson_x3f___redArg(
    mut v_inst_1195_: *mut leanh::LeanObject,
    mut v_x_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = l_Array_fromJson_x3f___redArg___closed__9;
    if leanh::lean_obj_tag(v_x_1196_) == 4 {
        let mut v_elems_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1199_: usize = 0;
        let mut v___x_1200_: usize = 0;
        let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_1198_ = leanh::lean_ctor_get(v_x_1196_, 0);
        leanh::lean_inc_ref(v_elems_1198_);
        leanh::lean_dec_ref_known(v_x_1196_, 1);
        v_sz_1199_ = lean_array_size(v_elems_1198_);
        v___x_1200_ = 0usize;
        v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1197_,
            v_inst_1195_,
            v_sz_1199_,
            v___x_1200_,
            v_elems_1198_,
        );
        return v___x_1201_;
    } else {
        let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1195_);
        v___x_1202_ = l_Array_fromJson_x3f___redArg___closed__10;
        v___x_1203_ = leanh::lean_unsigned_to_nat(80);
        v___x_1204_ = l_Lean_Json_pretty(v_x_1196_, v___x_1203_);
        v___x_1205_ = lean_string_append(v___x_1202_, v___x_1204_);
        leanh::lean_dec_ref(v___x_1204_);
        v___x_1206_ = l_Array_fromJson_x3f___redArg___closed__11;
        v___x_1207_ = lean_string_append(v___x_1205_, v___x_1206_);
        v___x_1208_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1208_, 0, v___x_1207_);
        return v___x_1208_;
    }
}
pub unsafe fn l_Array_fromJson_x3f(
    mut v_00_u03b1_1209_: *mut leanh::LeanObject,
    mut v_inst_1210_: *mut leanh::LeanObject,
    mut v_x_1211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Array_fromJson_x3f___redArg(v_inst_1210_, v_x_1211_);
    return v___x_1212_;
}
pub unsafe fn l_Lean_instFromJsonArray___redArg(
    mut v_inst_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ =
        leanh::lean_alloc_closure(l_Array_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1214_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1214_, 1, v_inst_1213_);
    return v___x_1214_;
}
pub unsafe fn l_Lean_instFromJsonArray(
    mut v_00_u03b1_1215_: *mut leanh::LeanObject,
    mut v_inst_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ =
        leanh::lean_alloc_closure(l_Array_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1217_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1217_, 1, v_inst_1216_);
    return v___x_1217_;
}
pub unsafe fn l_Array_toJson___redArg___lam__0(
    mut v_inst_1218_: *mut leanh::LeanObject,
    mut v_x_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = leanh::lean_apply_1(v_inst_1218_, v_x_1219_);
    return v___x_1220_;
}
pub unsafe fn l_Array_toJson___redArg(
    mut v_inst_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1242_ = leanh::lean_alloc_closure(
        l_Array_toJson___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1242_, 0, v_inst_1240_);
    v___x_1243_ = l_Array_toJson___redArg___closed__9;
    v_sz_1244_ = lean_array_size(v_a_1241_);
    v___x_1245_ = 0usize;
    v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1243_,
        v___f_1242_,
        v_sz_1244_,
        v___x_1245_,
        v_a_1241_,
    );
    v___x_1247_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1247_, 0, v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Array_toJson(
    mut v_00_u03b1_1248_: *mut leanh::LeanObject,
    mut v_inst_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Array_toJson___redArg(v_inst_1249_, v_a_1250_);
    return v___x_1251_;
}
pub unsafe fn l_Lean_instToJsonArray___redArg(
    mut v_inst_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1253_ = leanh::lean_alloc_closure(l_Array_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1253_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1253_, 1, v_inst_1252_);
    return v___x_1253_;
}
pub unsafe fn l_Lean_instToJsonArray(
    mut v_00_u03b1_1254_: *mut leanh::LeanObject,
    mut v_inst_1255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = leanh::lean_alloc_closure(l_Array_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1256_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1256_, 1, v_inst_1255_);
    return v___x_1256_;
}
pub unsafe fn l_List_fromJson_x3f___redArg(
    mut v_inst_1257_: *mut leanh::LeanObject,
    mut v_j_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1263_: u8 = 0;
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut v_a_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1259_ = l_Array_fromJson_x3f___redArg(v_inst_1257_, v_j_1258_);
                if leanh::lean_obj_tag(v___x_1259_) == 0 {
                    v_a_1260_ = leanh::lean_ctor_get(v___x_1259_, 0);
                    v_isSharedCheck_1267_ = (!leanh::lean_is_exclusive(v___x_1259_)) as u8;
                    if v_isSharedCheck_1267_ == 0 {
                        v___x_1262_ = v___x_1259_;
                        v_isShared_1263_ = v_isSharedCheck_1267_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1260_);
                        leanh::lean_dec(v___x_1259_);
                        v___x_1262_ = leanh::lean_box(0);
                        v_isShared_1263_ = v_isSharedCheck_1267_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1268_ = leanh::lean_ctor_get(v___x_1259_, 0);
                    v_isSharedCheck_1276_ = (!leanh::lean_is_exclusive(v___x_1259_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1270_ = v___x_1259_;
                        v_isShared_1271_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1268_);
                        leanh::lean_dec(v___x_1259_);
                        v___x_1270_ = leanh::lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1263_ == 0 {
                    v___x_1265_ = v___x_1262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
                    v___x_1265_ = v_reuseFailAlloc_1266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1265_;
            }
            3 => {
                v___x_1272_ = lean_array_to_list(v_a_1268_);
                if v_isShared_1271_ == 0 {
                    leanh::lean_ctor_set(v___x_1270_, 0, v___x_1272_);
                    v___x_1274_ = v___x_1270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
                    v___x_1274_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_fromJson_x3f(
    mut v_00_u03b1_1277_: *mut leanh::LeanObject,
    mut v_inst_1278_: *mut leanh::LeanObject,
    mut v_j_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_List_fromJson_x3f___redArg(v_inst_1278_, v_j_1279_);
    return v___x_1280_;
}
pub unsafe fn l_Lean_instFromJsonList___redArg(
    mut v_inst_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ =
        leanh::lean_alloc_closure(l_List_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1282_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1282_, 1, v_inst_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_instFromJsonList(
    mut v_00_u03b1_1283_: *mut leanh::LeanObject,
    mut v_inst_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ =
        leanh::lean_alloc_closure(l_List_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1285_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1285_, 1, v_inst_1284_);
    return v___x_1285_;
}
pub unsafe fn l_List_toJson___redArg(
    mut v_inst_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = lean_array_mk(v_a_1287_);
    v___x_1289_ = l_Array_toJson___redArg(v_inst_1286_, v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn l_List_toJson(
    mut v_00_u03b1_1290_: *mut leanh::LeanObject,
    mut v_inst_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ = l_List_toJson___redArg(v_inst_1291_, v_a_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_instToJsonList___redArg(
    mut v_inst_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = leanh::lean_alloc_closure(l_List_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1295_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1295_, 1, v_inst_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Lean_instToJsonList(
    mut v_00_u03b1_1296_: *mut leanh::LeanObject,
    mut v_inst_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = leanh::lean_alloc_closure(l_List_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1298_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1298_, 1, v_inst_1297_);
    return v___x_1298_;
}
pub unsafe fn l_Option_fromJson_x3f___redArg(
    mut v_inst_1301_: *mut leanh::LeanObject,
    mut v_x_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut v_a_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1302_) == 0 {
                    leanh::lean_dec_ref(v_inst_1301_);
                    v___x_1303_ = l_Option_fromJson_x3f___redArg___closed__0;
                    return v___x_1303_;
                } else {
                    v___x_1304_ = leanh::lean_apply_1(v_inst_1301_, v_x_1302_);
                    if leanh::lean_obj_tag(v___x_1304_) == 0 {
                        v_a_1305_ = leanh::lean_ctor_get(v___x_1304_, 0);
                        v_isSharedCheck_1312_ =
                            (!leanh::lean_is_exclusive(v___x_1304_)) as u8;
                        if v_isSharedCheck_1312_ == 0 {
                            v___x_1307_ = v___x_1304_;
                            v_isShared_1308_ = v_isSharedCheck_1312_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1305_);
                            leanh::lean_dec(v___x_1304_);
                            v___x_1307_ = leanh::lean_box(0);
                            v_isShared_1308_ = v_isSharedCheck_1312_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1313_ = leanh::lean_ctor_get(v___x_1304_, 0);
                        v_isSharedCheck_1321_ =
                            (!leanh::lean_is_exclusive(v___x_1304_)) as u8;
                        if v_isSharedCheck_1321_ == 0 {
                            v___x_1315_ = v___x_1304_;
                            v_isShared_1316_ = v_isSharedCheck_1321_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1313_);
                            leanh::lean_dec(v___x_1304_);
                            v___x_1315_ = leanh::lean_box(0);
                            v_isShared_1316_ = v_isSharedCheck_1321_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1308_ == 0 {
                    v___x_1310_ = v___x_1307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
                    v___x_1310_ = v_reuseFailAlloc_1311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1310_;
            }
            3 => {
                v___x_1317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1317_, 0, v_a_1313_);
                if v_isShared_1316_ == 0 {
                    leanh::lean_ctor_set(v___x_1315_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f(
    mut v_00_u03b1_1322_: *mut leanh::LeanObject,
    mut v_inst_1323_: *mut leanh::LeanObject,
    mut v_x_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Option_fromJson_x3f___redArg(v_inst_1323_, v_x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_Lean_instFromJsonOption___redArg(
    mut v_inst_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ =
        leanh::lean_alloc_closure(l_Option_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1327_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1327_, 1, v_inst_1326_);
    return v___x_1327_;
}
pub unsafe fn l_Lean_instFromJsonOption(
    mut v_00_u03b1_1328_: *mut leanh::LeanObject,
    mut v_inst_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ =
        leanh::lean_alloc_closure(l_Option_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1330_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1330_, 1, v_inst_1329_);
    return v___x_1330_;
}
pub unsafe fn l_Option_toJson___redArg(
    mut v_inst_1331_: *mut leanh::LeanObject,
    mut v_x_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1332_) == 0 {
        let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1331_);
        v___x_1333_ = leanh::lean_box(0);
        return v___x_1333_;
    } else {
        let mut v_val_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1334_ = leanh::lean_ctor_get(v_x_1332_, 0);
        leanh::lean_inc(v_val_1334_);
        leanh::lean_dec_ref_known(v_x_1332_, 1);
        v___x_1335_ = leanh::lean_apply_1(v_inst_1331_, v_val_1334_);
        return v___x_1335_;
    }
}
pub unsafe fn l_Option_toJson(
    mut v_00_u03b1_1336_: *mut leanh::LeanObject,
    mut v_inst_1337_: *mut leanh::LeanObject,
    mut v_x_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = l_Option_toJson___redArg(v_inst_1337_, v_x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Lean_instToJsonOption___redArg(
    mut v_inst_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = leanh::lean_alloc_closure(l_Option_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1341_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1341_, 1, v_inst_1340_);
    return v___x_1341_;
}
pub unsafe fn l_Lean_instToJsonOption(
    mut v_00_u03b1_1342_: *mut leanh::LeanObject,
    mut v_inst_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ = leanh::lean_alloc_closure(l_Option_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1344_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1344_, 1, v_inst_1343_);
    return v___x_1344_;
}
pub unsafe fn l_Prod_fromJson_x3f___redArg(
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_inst_1347_: *mut leanh::LeanObject,
    mut v_x_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_j_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elems_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_a_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut v_a_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1348_) == 4 {
                    v_elems_1358_ = leanh::lean_ctor_get(v_x_1348_, 0);
                    v___x_1359_ = lean_array_get_size(v_elems_1358_);
                    v___x_1360_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1361_ = lean_nat_dec_eq(v___x_1359_, v___x_1360_);
                    if v___x_1361_ == 0 {
                        leanh::lean_dec_ref(v_inst_1347_);
                        leanh::lean_dec_ref(v_inst_1346_);
                        v_j_1350_ = v_x_1348_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_elems_1358_);
                        leanh::lean_dec_ref_known(v_x_1348_, 1);
                        v___x_1362_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1363_ = lean_array_fget_borrowed(v_elems_1358_, v___x_1362_);
                        leanh::lean_inc(v___x_1363_);
                        v___x_1364_ = leanh::lean_apply_1(v_inst_1346_, v___x_1363_);
                        if leanh::lean_obj_tag(v___x_1364_) == 0 {
                            leanh::lean_dec_ref(v_elems_1358_);
                            leanh::lean_dec_ref(v_inst_1347_);
                            v_a_1365_ = leanh::lean_ctor_get(v___x_1364_, 0);
                            v_isSharedCheck_1372_ =
                                (!leanh::lean_is_exclusive(v___x_1364_)) as u8;
                            if v_isSharedCheck_1372_ == 0 {
                                v___x_1367_ = v___x_1364_;
                                v_isShared_1368_ = v_isSharedCheck_1372_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1365_);
                                leanh::lean_dec(v___x_1364_);
                                v___x_1367_ = leanh::lean_box(0);
                                v_isShared_1368_ = v_isSharedCheck_1372_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_1373_ = leanh::lean_ctor_get(v___x_1364_, 0);
                            leanh::lean_inc(v_a_1373_);
                            leanh::lean_dec_ref_known(v___x_1364_, 1);
                            v___x_1374_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1375_ = lean_array_fget(v_elems_1358_, v___x_1374_);
                            leanh::lean_dec_ref(v_elems_1358_);
                            v___x_1376_ = leanh::lean_apply_1(v_inst_1347_, v___x_1375_);
                            if leanh::lean_obj_tag(v___x_1376_) == 0 {
                                leanh::lean_dec(v_a_1373_);
                                v_a_1377_ = leanh::lean_ctor_get(v___x_1376_, 0);
                                v_isSharedCheck_1384_ =
                                    (!leanh::lean_is_exclusive(v___x_1376_)) as u8;
                                if v_isSharedCheck_1384_ == 0 {
                                    v___x_1379_ = v___x_1376_;
                                    v_isShared_1380_ = v_isSharedCheck_1384_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1377_);
                                    leanh::lean_dec(v___x_1376_);
                                    v___x_1379_ = leanh::lean_box(0);
                                    v_isShared_1380_ = v_isSharedCheck_1384_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_1385_ = leanh::lean_ctor_get(v___x_1376_, 0);
                                v_isSharedCheck_1393_ =
                                    (!leanh::lean_is_exclusive(v___x_1376_)) as u8;
                                if v_isSharedCheck_1393_ == 0 {
                                    v___x_1387_ = v___x_1376_;
                                    v_isShared_1388_ = v_isSharedCheck_1393_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1385_);
                                    leanh::lean_dec(v___x_1376_);
                                    v___x_1387_ = leanh::lean_box(0);
                                    v_isShared_1388_ = v_isSharedCheck_1393_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_1347_);
                    leanh::lean_dec_ref(v_inst_1346_);
                    v_j_1350_ = v_x_1348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1351_ = l_Prod_fromJson_x3f___redArg___closed__0;
                v___x_1352_ = leanh::lean_unsigned_to_nat(80);
                v___x_1353_ = l_Lean_Json_pretty(v_j_1350_, v___x_1352_);
                v___x_1354_ = lean_string_append(v___x_1351_, v___x_1353_);
                leanh::lean_dec_ref(v___x_1353_);
                v___x_1355_ = l_Array_fromJson_x3f___redArg___closed__11;
                v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
                v___x_1357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                return v___x_1357_;
            }
            2 => {
                if v_isShared_1368_ == 0 {
                    v___x_1370_ = v___x_1367_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1370_;
            }
            4 => {
                if v_isShared_1380_ == 0 {
                    v___x_1382_ = v___x_1379_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1383_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
                    v___x_1382_ = v_reuseFailAlloc_1383_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1382_;
            }
            6 => {
                v___x_1389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1389_, 0, v_a_1373_);
                leanh::lean_ctor_set(v___x_1389_, 1, v_a_1385_);
                if v_isShared_1388_ == 0 {
                    leanh::lean_ctor_set(v___x_1387_, 0, v___x_1389_);
                    v___x_1391_ = v___x_1387_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1392_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_fromJson_x3f(
    mut v_00_u03b1_1394_: *mut leanh::LeanObject,
    mut v_00_u03b2_1395_: *mut leanh::LeanObject,
    mut v_inst_1396_: *mut leanh::LeanObject,
    mut v_inst_1397_: *mut leanh::LeanObject,
    mut v_x_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Prod_fromJson_x3f___redArg(v_inst_1396_, v_inst_1397_, v_x_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_instFromJsonProd___redArg(
    mut v_inst_1400_: *mut leanh::LeanObject,
    mut v_inst_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ =
        leanh::lean_alloc_closure(l_Prod_fromJson_x3f as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1402_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1402_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1402_, 2, v_inst_1400_);
    leanh::lean_closure_set(v___x_1402_, 3, v_inst_1401_);
    return v___x_1402_;
}
pub unsafe fn l_Lean_instFromJsonProd(
    mut v_00_u03b1_1403_: *mut leanh::LeanObject,
    mut v_00_u03b2_1404_: *mut leanh::LeanObject,
    mut v_inst_1405_: *mut leanh::LeanObject,
    mut v_inst_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ =
        leanh::lean_alloc_closure(l_Prod_fromJson_x3f as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1407_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1407_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1407_, 2, v_inst_1405_);
    leanh::lean_closure_set(v___x_1407_, 3, v_inst_1406_);
    return v___x_1407_;
}
pub unsafe fn l_Prod_toJson___redArg(
    mut v_inst_1408_: *mut leanh::LeanObject,
    mut v_inst_1409_: *mut leanh::LeanObject,
    mut v_x_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1411_ = leanh::lean_ctor_get(v_x_1410_, 0);
    leanh::lean_inc(v_fst_1411_);
    v_snd_1412_ = leanh::lean_ctor_get(v_x_1410_, 1);
    leanh::lean_inc(v_snd_1412_);
    leanh::lean_dec_ref(v_x_1410_);
    v___x_1413_ = leanh::lean_apply_1(v_inst_1408_, v_fst_1411_);
    v___x_1414_ = leanh::lean_apply_1(v_inst_1409_, v_snd_1412_);
    v___x_1415_ = leanh::lean_unsigned_to_nat(2);
    v___x_1416_ = lean_mk_empty_array_with_capacity(v___x_1415_);
    v___x_1417_ = lean_array_push(v___x_1416_, v___x_1413_);
    v___x_1418_ = lean_array_push(v___x_1417_, v___x_1414_);
    v___x_1419_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1419_, 0, v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn l_Prod_toJson(
    mut v_00_u03b1_1420_: *mut leanh::LeanObject,
    mut v_00_u03b2_1421_: *mut leanh::LeanObject,
    mut v_inst_1422_: *mut leanh::LeanObject,
    mut v_inst_1423_: *mut leanh::LeanObject,
    mut v_x_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1425_ = l_Prod_toJson___redArg(v_inst_1422_, v_inst_1423_, v_x_1424_);
    return v___x_1425_;
}
pub unsafe fn l_Lean_instToJsonProd___redArg(
    mut v_inst_1426_: *mut leanh::LeanObject,
    mut v_inst_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = leanh::lean_alloc_closure(l_Prod_toJson as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1428_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1428_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1428_, 2, v_inst_1426_);
    leanh::lean_closure_set(v___x_1428_, 3, v_inst_1427_);
    return v___x_1428_;
}
pub unsafe fn l_Lean_instToJsonProd(
    mut v_00_u03b1_1429_: *mut leanh::LeanObject,
    mut v_00_u03b2_1430_: *mut leanh::LeanObject,
    mut v_inst_1431_: *mut leanh::LeanObject,
    mut v_inst_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = leanh::lean_alloc_closure(l_Prod_toJson as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_1433_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1433_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1433_, 2, v_inst_1431_);
    leanh::lean_closure_set(v___x_1433_, 3, v_inst_1432_);
    return v___x_1433_;
}
pub unsafe fn l_Lean_Name_fromJson_x3f(
    mut v_j_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_a_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_j_1438_);
                v___x_1439_ = l_Lean_Json_getStr_x3f(v_j_1438_);
                if leanh::lean_obj_tag(v___x_1439_) == 0 {
                    leanh::lean_dec(v_j_1438_);
                    v_a_1440_ = leanh::lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1447_ = (!leanh::lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1447_ == 0 {
                        v___x_1442_ = v___x_1439_;
                        v_isShared_1443_ = v_isSharedCheck_1447_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1440_);
                        leanh::lean_dec(v___x_1439_);
                        v___x_1442_ = leanh::lean_box(0);
                        v_isShared_1443_ = v_isSharedCheck_1447_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1448_ = leanh::lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1469_ = (!leanh::lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1469_ == 0 {
                        v___x_1450_ = v___x_1439_;
                        v_isShared_1451_ = v_isSharedCheck_1469_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1448_);
                        leanh::lean_dec(v___x_1439_);
                        v___x_1450_ = leanh::lean_box(0);
                        v_isShared_1451_ = v_isSharedCheck_1469_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1443_ == 0 {
                    v___x_1445_ = v___x_1442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
                    v___x_1445_ = v_reuseFailAlloc_1446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1445_;
            }
            3 => {
                v___x_1452_ = l_Lean_Name_fromJson_x3f___closed__0;
                v___x_1453_ = lean_string_dec_eq(v_a_1448_, v___x_1452_);
                if v___x_1453_ == 0 {
                    v___x_1454_ = l_String_toName(v_a_1448_);
                    v___x_1455_ = l_Lean_Name_isAnonymous(v___x_1454_);
                    if v___x_1455_ == 0 {
                        leanh::lean_dec(v_j_1438_);
                        if v_isShared_1451_ == 0 {
                            leanh::lean_ctor_set(v___x_1450_, 0, v___x_1454_);
                            v___x_1457_ = v___x_1450_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1458_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1454_);
                            v___x_1457_ = v_reuseFailAlloc_1458_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1454_);
                        v___x_1459_ = l_Lean_Name_fromJson_x3f___closed__1;
                        v___x_1460_ = leanh::lean_unsigned_to_nat(80);
                        v___x_1461_ = l_Lean_Json_pretty(v_j_1438_, v___x_1460_);
                        v___x_1462_ = lean_string_append(v___x_1459_, v___x_1461_);
                        leanh::lean_dec_ref(v___x_1461_);
                        v___x_1463_ = l_Array_fromJson_x3f___redArg___closed__11;
                        v___x_1464_ = lean_string_append(v___x_1462_, v___x_1463_);
                        if v_isShared_1451_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1450_, 0);
                            leanh::lean_ctor_set(v___x_1450_, 0, v___x_1464_);
                            v___x_1466_ = v___x_1450_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1467_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
                            v___x_1466_ = v_reuseFailAlloc_1467_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1450_);
                    leanh::lean_dec(v_a_1448_);
                    leanh::lean_dec(v_j_1438_);
                    v___x_1468_ = l_Lean_Name_fromJson_x3f___closed__2;
                    return v___x_1468_;
                }
            }
            4 => {
                return v___x_1457_;
            }
            5 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonName___lam__0(
    mut v_n_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1473_: u8 = 0;
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = 1;
    v___x_1474_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1472_, v___x_1473_);
    v___x_1475_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1475_, 0, v___x_1474_);
    return v___x_1475_;
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___redArg___lam__0(
    mut v_inst_1478_: *mut leanh::LeanObject,
    mut v_m_1479_: *mut leanh::LeanObject,
    mut v_k_1480_: *mut leanh::LeanObject,
    mut v_v_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v_n_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_a_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut v_a_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1521_: u8 = 0;
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1482_ = l_Lean_Name_fromJson_x3f___closed__0;
                v___x_1483_ = lean_string_dec_eq(v_k_1480_, v___x_1482_);
                if v___x_1483_ == 0 {
                    leanh::lean_inc_ref(v_k_1480_);
                    v_n_1484_ = l_String_toName(v_k_1480_);
                    v___x_1485_ = l_Lean_Name_isAnonymous(v_n_1484_);
                    if v___x_1485_ == 0 {
                        leanh::lean_dec_ref(v_k_1480_);
                        v___x_1486_ = leanh::lean_apply_1(v_inst_1478_, v_v_1481_);
                        if leanh::lean_obj_tag(v___x_1486_) == 0 {
                            leanh::lean_dec(v_n_1484_);
                            leanh::lean_dec(v_m_1479_);
                            v_a_1487_ = leanh::lean_ctor_get(v___x_1486_, 0);
                            v_isSharedCheck_1494_ =
                                (!leanh::lean_is_exclusive(v___x_1486_)) as u8;
                            if v_isSharedCheck_1494_ == 0 {
                                v___x_1489_ = v___x_1486_;
                                v_isShared_1490_ = v_isSharedCheck_1494_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1487_);
                                leanh::lean_dec(v___x_1486_);
                                v___x_1489_ = leanh::lean_box(0);
                                v_isShared_1490_ = v_isSharedCheck_1494_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1495_ = leanh::lean_ctor_get(v___x_1486_, 0);
                            v_isSharedCheck_1503_ =
                                (!leanh::lean_is_exclusive(v___x_1486_)) as u8;
                            if v_isSharedCheck_1503_ == 0 {
                                v___x_1497_ = v___x_1486_;
                                v_isShared_1498_ = v_isSharedCheck_1503_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1495_);
                                leanh::lean_dec(v___x_1486_);
                                v___x_1497_ = leanh::lean_box(0);
                                v_isShared_1498_ = v_isSharedCheck_1503_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_n_1484_);
                        leanh::lean_dec(v_v_1481_);
                        leanh::lean_dec(v_m_1479_);
                        leanh::lean_dec_ref(v_inst_1478_);
                        v___x_1504_ = l_Lean_Name_fromJson_x3f___closed__1;
                        v___x_1505_ = lean_string_append(v___x_1504_, v_k_1480_);
                        leanh::lean_dec_ref(v_k_1480_);
                        v___x_1506_ = l_Array_fromJson_x3f___redArg___closed__11;
                        v___x_1507_ = lean_string_append(v___x_1505_, v___x_1506_);
                        v___x_1508_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
                        return v___x_1508_;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_1480_);
                    v___x_1509_ = leanh::lean_apply_1(v_inst_1478_, v_v_1481_);
                    if leanh::lean_obj_tag(v___x_1509_) == 0 {
                        leanh::lean_dec(v_m_1479_);
                        v_a_1510_ = leanh::lean_ctor_get(v___x_1509_, 0);
                        v_isSharedCheck_1517_ =
                            (!leanh::lean_is_exclusive(v___x_1509_)) as u8;
                        if v_isSharedCheck_1517_ == 0 {
                            v___x_1512_ = v___x_1509_;
                            v_isShared_1513_ = v_isSharedCheck_1517_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1510_);
                            leanh::lean_dec(v___x_1509_);
                            v___x_1512_ = leanh::lean_box(0);
                            v_isShared_1513_ = v_isSharedCheck_1517_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1518_ = leanh::lean_ctor_get(v___x_1509_, 0);
                        v_isSharedCheck_1527_ =
                            (!leanh::lean_is_exclusive(v___x_1509_)) as u8;
                        if v_isSharedCheck_1527_ == 0 {
                            v___x_1520_ = v___x_1509_;
                            v_isShared_1521_ = v_isSharedCheck_1527_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1518_);
                            leanh::lean_dec(v___x_1509_);
                            v___x_1520_ = leanh::lean_box(0);
                            v_isShared_1521_ = v_isSharedCheck_1527_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1492_;
            }
            3 => {
                v___x_1499_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1484_, v_a_1495_, v_m_1479_);
                if v_isShared_1498_ == 0 {
                    leanh::lean_ctor_set(v___x_1497_, 0, v___x_1499_);
                    v___x_1501_ = v___x_1497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
                    v___x_1501_ = v_reuseFailAlloc_1502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1501_;
            }
            5 => {
                if v_isShared_1513_ == 0 {
                    v___x_1515_ = v___x_1512_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
                    v___x_1515_ = v_reuseFailAlloc_1516_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1515_;
            }
            7 => {
                v___x_1522_ = leanh::lean_box(0);
                v___x_1523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1522_, v_a_1518_, v_m_1479_);
                if v_isShared_1521_ == 0 {
                    leanh::lean_ctor_set(v___x_1520_, 0, v___x_1523_);
                    v___x_1525_ = v___x_1520_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___redArg(
    mut v_inst_1529_: *mut leanh::LeanObject,
    mut v_x_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Array_fromJson_x3f___redArg___closed__9;
    if leanh::lean_obj_tag(v_x_1530_) == 5 {
        let mut v_kvPairs_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_kvPairs_1532_ = leanh::lean_ctor_get(v_x_1530_, 0);
        leanh::lean_inc(v_kvPairs_1532_);
        leanh::lean_dec_ref_known(v_x_1530_, 1);
        v___f_1533_ = leanh::lean_alloc_closure(
            l_Lean_NameMap_fromJson_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        leanh::lean_closure_set(v___f_1533_, 0, v_inst_1529_);
        v___x_1534_ = leanh::lean_box(1);
        v___x_1535_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
            v___x_1531_,
            v___f_1533_,
            v___x_1534_,
            v_kvPairs_1532_,
        );
        return v___x_1535_;
    } else {
        let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1529_);
        v___x_1536_ = l_Lean_NameMap_fromJson_x3f___redArg___closed__0;
        v___x_1537_ = leanh::lean_unsigned_to_nat(80);
        v___x_1538_ = l_Lean_Json_pretty(v_x_1530_, v___x_1537_);
        v___x_1539_ = lean_string_append(v___x_1536_, v___x_1538_);
        leanh::lean_dec_ref(v___x_1538_);
        v___x_1540_ = l_Array_fromJson_x3f___redArg___closed__11;
        v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
        v___x_1542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
        return v___x_1542_;
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f(
    mut v_00_u03b1_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_x_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_NameMap_fromJson_x3f___redArg(v_inst_1544_, v_x_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_instFromJsonNameMap___redArg(
    mut v_inst_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = leanh::lean_alloc_closure(
        l_Lean_NameMap_fromJson_x3f as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1548_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1548_, 1, v_inst_1547_);
    return v___x_1548_;
}
pub unsafe fn l_Lean_instFromJsonNameMap(
    mut v_00_u03b1_1549_: *mut leanh::LeanObject,
    mut v_inst_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = leanh::lean_alloc_closure(
        l_Lean_NameMap_fromJson_x3f as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1551_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1551_, 1, v_inst_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Lean_NameMap_toJson___redArg___lam__0(
    mut v_inst_1553_: *mut leanh::LeanObject,
    mut v_n_1554_: *mut leanh::LeanObject,
    mut v_k_1555_: *mut leanh::LeanObject,
    mut v_v_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_Lean_NameMap_toJson___redArg___lam__0___closed__0;
    v___x_1558_ = 1;
    v___x_1559_ = l_Lean_Name_toString(v_k_1555_, v___x_1558_);
    v___x_1560_ = leanh::lean_apply_1(v_inst_1553_, v_v_1556_);
    v___x_1561_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v___x_1557_,
        v___x_1559_,
        v___x_1560_,
        v_n_1554_,
    );
    return v___x_1561_;
}
pub unsafe fn l_Lean_NameMap_toJson___redArg(
    mut v_inst_1562_: *mut leanh::LeanObject,
    mut v_m_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1564_ = leanh::lean_alloc_closure(
        l_Lean_NameMap_toJson___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1564_, 0, v_inst_1562_);
    v___x_1565_ = leanh::lean_box(1);
    v___x_1566_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1564_, v___x_1565_, v_m_1563_);
    v___x_1567_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1567_, 0, v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Lean_NameMap_toJson(
    mut v_00_u03b1_1568_: *mut leanh::LeanObject,
    mut v_inst_1569_: *mut leanh::LeanObject,
    mut v_m_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1571_ = l_Lean_NameMap_toJson___redArg(v_inst_1569_, v_m_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lean_instToJsonNameMap___redArg(
    mut v_inst_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ =
        leanh::lean_alloc_closure(l_Lean_NameMap_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1573_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1573_, 1, v_inst_1572_);
    return v___x_1573_;
}
pub unsafe fn l_Lean_instToJsonNameMap(
    mut v_00_u03b1_1574_: *mut leanh::LeanObject,
    mut v_inst_1575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1576_ =
        leanh::lean_alloc_closure(l_Lean_NameMap_toJson as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_1576_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1576_, 1, v_inst_1575_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_bignumFromJson_x3f(
    mut v_j_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_j_1578_);
                v___x_1579_ = l_Lean_Json_getStr_x3f(v_j_1578_);
                if leanh::lean_obj_tag(v___x_1579_) == 0 {
                    leanh::lean_dec(v_j_1578_);
                    v_a_1580_ = leanh::lean_ctor_get(v___x_1579_, 0);
                    v_isSharedCheck_1587_ = (!leanh::lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1582_ = v___x_1579_;
                        v_isShared_1583_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1580_);
                        leanh::lean_dec(v___x_1579_);
                        v___x_1582_ = leanh::lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1588_ = leanh::lean_ctor_get(v___x_1579_, 0);
                    v_isSharedCheck_1606_ = (!leanh::lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1606_ == 0 {
                        v___x_1590_ = v___x_1579_;
                        v_isShared_1591_ = v_isSharedCheck_1606_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1588_);
                        leanh::lean_dec(v___x_1579_);
                        v___x_1590_ = leanh::lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1606_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1583_ == 0 {
                    v___x_1585_ = v___x_1582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
                    v___x_1585_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1585_;
            }
            3 => {
                v___x_1592_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_a_1588_);
                leanh::lean_dec(v_a_1588_);
                if leanh::lean_obj_tag(v___x_1592_) == 1 {
                    leanh::lean_dec(v_j_1578_);
                    v_val_1593_ = leanh::lean_ctor_get(v___x_1592_, 0);
                    leanh::lean_inc(v_val_1593_);
                    leanh::lean_dec_ref_known(v___x_1592_, 1);
                    if v_isShared_1591_ == 0 {
                        leanh::lean_ctor_set(v___x_1590_, 0, v_val_1593_);
                        v___x_1595_ = v___x_1590_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_val_1593_);
                        v___x_1595_ = v_reuseFailAlloc_1596_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1592_);
                    v___x_1597_ = l_Lean_bignumFromJson_x3f___closed__0;
                    v___x_1598_ = leanh::lean_unsigned_to_nat(80);
                    v___x_1599_ = l_Lean_Json_pretty(v_j_1578_, v___x_1598_);
                    v___x_1600_ = lean_string_append(v___x_1597_, v___x_1599_);
                    leanh::lean_dec_ref(v___x_1599_);
                    v___x_1601_ = l_Array_fromJson_x3f___redArg___closed__11;
                    v___x_1602_ = lean_string_append(v___x_1600_, v___x_1601_);
                    if v_isShared_1591_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1590_, 0);
                        leanh::lean_ctor_set(v___x_1590_, 0, v___x_1602_);
                        v___x_1604_ = v___x_1590_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1605_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
                        v___x_1604_ = v_reuseFailAlloc_1605_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1595_;
            }
            5 => {
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_bignumToJson(
    mut v_n_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_Nat_reprFast(v_n_1607_);
    v___x_1609_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn _init_l_USize_fromJson_x3f___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_System_Platform_numBits;
    v___x_1611_ = leanh::lean_unsigned_to_nat(2);
    v___x_1612_ = lean_nat_pow(v___x_1611_, v___x_1610_);
    return v___x_1612_;
}
pub unsafe fn l_USize_fromJson_x3f(
    mut v_j_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_a_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_j_1615_);
                v___x_1616_ = l_Lean_bignumFromJson_x3f(v_j_1615_);
                if leanh::lean_obj_tag(v___x_1616_) == 0 {
                    leanh::lean_dec(v_j_1615_);
                    v_a_1617_ = leanh::lean_ctor_get(v___x_1616_, 0);
                    v_isSharedCheck_1624_ = (!leanh::lean_is_exclusive(v___x_1616_)) as u8;
                    if v_isSharedCheck_1624_ == 0 {
                        v___x_1619_ = v___x_1616_;
                        v_isShared_1620_ = v_isSharedCheck_1624_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1617_);
                        leanh::lean_dec(v___x_1616_);
                        v___x_1619_ = leanh::lean_box(0);
                        v_isShared_1620_ = v_isSharedCheck_1624_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1625_ = leanh::lean_ctor_get(v___x_1616_, 0);
                    v_isSharedCheck_1645_ = (!leanh::lean_is_exclusive(v___x_1616_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1627_ = v___x_1616_;
                        v_isShared_1628_ = v_isSharedCheck_1645_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1625_);
                        leanh::lean_dec(v___x_1616_);
                        v___x_1627_ = leanh::lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1645_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1620_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
                    v___x_1622_ = v_reuseFailAlloc_1623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1622_;
            }
            3 => {
                v___x_1629_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_USize_fromJson_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_USize_fromJson_x3f___closed__0_once),
                    _init_l_USize_fromJson_x3f___closed__0,
                );
                v___x_1630_ = lean_nat_dec_le(v___x_1629_, v_a_1625_);
                if v___x_1630_ == 0 {
                    leanh::lean_dec(v_j_1615_);
                    v___x_1631_ = lean_usize_of_nat(v_a_1625_);
                    leanh::lean_dec(v_a_1625_);
                    v___x_1632_ = leanh::lean_box_usize(v___x_1631_);
                    if v_isShared_1628_ == 0 {
                        leanh::lean_ctor_set(v___x_1627_, 0, v___x_1632_);
                        v___x_1634_ = v___x_1627_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
                        v___x_1634_ = v_reuseFailAlloc_1635_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1625_);
                    v___x_1636_ = l_USize_fromJson_x3f___closed__1;
                    v___x_1637_ = leanh::lean_unsigned_to_nat(80);
                    v___x_1638_ = l_Lean_Json_pretty(v_j_1615_, v___x_1637_);
                    v___x_1639_ = lean_string_append(v___x_1636_, v___x_1638_);
                    leanh::lean_dec_ref(v___x_1638_);
                    v___x_1640_ = l_USize_fromJson_x3f___closed__2;
                    v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
                    if v_isShared_1628_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1627_, 0);
                        leanh::lean_ctor_set(v___x_1627_, 0, v___x_1641_);
                        v___x_1643_ = v___x_1627_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
                        v___x_1643_ = v_reuseFailAlloc_1644_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1634_;
            }
            5 => {
                return v___x_1643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonUSize___lam__0(
    mut v_v_1648_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = lean_usize_to_nat(v_v_1648_);
    v___x_1650_ = l_Lean_bignumToJson(v___x_1649_);
    return v___x_1650_;
}
pub unsafe fn l_Lean_instToJsonUSize___lam__0___boxed(
    mut v_v_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1652_: usize = 0;
    let mut v_res_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1652_ = leanh::lean_unbox_usize(v_v_1651_);
    leanh::lean_dec(v_v_1651_);
    v_res_1653_ = l_Lean_instToJsonUSize___lam__0(v_v_boxed_1652_);
    return v_res_1653_;
}
pub unsafe fn _init_l_UInt64_fromJson_x3f___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = leanh::lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_1656_;
}
pub unsafe fn l_UInt64_fromJson_x3f(
    mut v_j_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: u64 = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_j_1658_);
                v___x_1659_ = l_Lean_bignumFromJson_x3f(v_j_1658_);
                if leanh::lean_obj_tag(v___x_1659_) == 0 {
                    leanh::lean_dec(v_j_1658_);
                    v_a_1660_ = leanh::lean_ctor_get(v___x_1659_, 0);
                    v_isSharedCheck_1667_ = (!leanh::lean_is_exclusive(v___x_1659_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1659_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1660_);
                        leanh::lean_dec(v___x_1659_);
                        v___x_1662_ = leanh::lean_box(0);
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1668_ = leanh::lean_ctor_get(v___x_1659_, 0);
                    v_isSharedCheck_1688_ = (!leanh::lean_is_exclusive(v___x_1659_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v___x_1670_ = v___x_1659_;
                        v_isShared_1671_ = v_isSharedCheck_1688_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1668_);
                        leanh::lean_dec(v___x_1659_);
                        v___x_1670_ = leanh::lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1688_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1663_ == 0 {
                    v___x_1665_ = v___x_1662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1665_;
            }
            3 => {
                v___x_1672_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_UInt64_fromJson_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_UInt64_fromJson_x3f___closed__0_once),
                    _init_l_UInt64_fromJson_x3f___closed__0,
                );
                v___x_1673_ = lean_nat_dec_le(v___x_1672_, v_a_1668_);
                if v___x_1673_ == 0 {
                    leanh::lean_dec(v_j_1658_);
                    v___x_1674_ = lean_uint64_of_nat(v_a_1668_);
                    leanh::lean_dec(v_a_1668_);
                    v___x_1675_ = leanh::lean_box_uint64(v___x_1674_);
                    if v_isShared_1671_ == 0 {
                        leanh::lean_ctor_set(v___x_1670_, 0, v___x_1675_);
                        v___x_1677_ = v___x_1670_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1678_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
                        v___x_1677_ = v_reuseFailAlloc_1678_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1668_);
                    v___x_1679_ = l_USize_fromJson_x3f___closed__1;
                    v___x_1680_ = leanh::lean_unsigned_to_nat(80);
                    v___x_1681_ = l_Lean_Json_pretty(v_j_1658_, v___x_1680_);
                    v___x_1682_ = lean_string_append(v___x_1679_, v___x_1681_);
                    leanh::lean_dec_ref(v___x_1681_);
                    v___x_1683_ = l_UInt64_fromJson_x3f___closed__1;
                    v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
                    if v_isShared_1671_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1670_, 0);
                        leanh::lean_ctor_set(v___x_1670_, 0, v___x_1684_);
                        v___x_1686_ = v___x_1670_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1687_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
                        v___x_1686_ = v_reuseFailAlloc_1687_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1677_;
            }
            5 => {
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonUInt64___lam__0(
    mut v_v_1691_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = lean_uint64_to_nat(v_v_1691_);
    v___x_1693_ = l_Lean_bignumToJson(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Lean_instToJsonUInt64___lam__0___boxed(
    mut v_v_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1695_: u64 = 0;
    let mut v_res_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1695_ = leanh::lean_unbox_uint64(v_v_1694_);
    leanh::lean_dec_ref(v_v_1694_);
    v_res_1696_ = l_Lean_instToJsonUInt64___lam__0(v_v_boxed_1695_);
    return v_res_1696_;
}
pub unsafe fn l_Float_toJson(mut v_x_1699_: f64) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1704_: u8 = 0;
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_val_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1700_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_1699_);
                if leanh::lean_obj_tag(v___x_1700_) == 0 {
                    v_val_1701_ = leanh::lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1708_ = (!leanh::lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1703_ = v___x_1700_;
                        v_isShared_1704_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1701_);
                        leanh::lean_dec(v___x_1700_);
                        v___x_1703_ = leanh::lean_box(0);
                        v_isShared_1704_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_val_1709_ = leanh::lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1716_ = (!leanh::lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1716_ == 0 {
                        v___x_1711_ = v___x_1700_;
                        v_isShared_1712_ = v_isSharedCheck_1716_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1709_);
                        leanh::lean_dec(v___x_1700_);
                        v___x_1711_ = leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1716_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1704_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1703_, 3);
                    v___x_1706_ = v___x_1703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_val_1701_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            3 => {
                if v_isShared_1712_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1711_, 2);
                    v___x_1714_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1715_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_val_1709_);
                    v___x_1714_ = v_reuseFailAlloc_1715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Float_toJson___boxed(
    mut v_x_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1718_: f64 = 0.0;
    let mut v_res_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1718_ = leanh::lean_unbox_float(v_x_1717_);
    leanh::lean_dec_ref(v_x_1717_);
    v_res_1719_ = l_Float_toJson(v_x_boxed_1718_);
    return v_res_1719_;
}
pub unsafe fn l_Float_fromJson_x3f(
    mut v_x_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: f64 = 0.0;
    let mut v___x_1744_: f64 = 0.0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: f64 = 0.0;
    let mut v___x_1752_: f64 = 0.0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: f64 = 0.0;
    let mut v___x_1755_: f64 = 0.0;
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: f64 = 0.0;
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: f64 = 0.0;
    let mut v___x_1765_: f64 = 0.0;
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_n_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1775_: f64 = 0.0;
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1728_) {
                3 => {
                    v_s_1731_ = leanh::lean_ctor_get(v_x_1728_, 0);
                    v_isSharedCheck_1770_ = (!leanh::lean_is_exclusive(v_x_1728_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1733_ = v_x_1728_;
                        v_isShared_1734_ = v_isSharedCheck_1770_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1731_);
                        leanh::lean_dec(v_x_1728_);
                        v___x_1733_ = leanh::lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1770_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_n_1771_ = leanh::lean_ctor_get(v_x_1728_, 0);
                    v_isSharedCheck_1780_ = (!leanh::lean_is_exclusive(v_x_1728_)) as u8;
                    if v_isSharedCheck_1780_ == 0 {
                        v___x_1773_ = v_x_1728_;
                        v_isShared_1774_ = v_isSharedCheck_1780_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_1771_);
                        leanh::lean_dec(v_x_1728_);
                        v___x_1773_ = leanh::lean_box(0);
                        v_isShared_1774_ = v_isSharedCheck_1780_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_1728_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1730_ = l_Float_fromJson_x3f___closed__1;
                return v___x_1730_;
            }
            2 => {
                v___x_1735_ = l_Float_fromJson_x3f___closed__2;
                v___x_1736_ = lean_string_dec_eq(v_s_1731_, v___x_1735_);
                if v___x_1736_ == 0 {
                    v___x_1737_ = l_Float_fromJson_x3f___closed__3;
                    v___x_1738_ = lean_string_dec_eq(v_s_1731_, v___x_1737_);
                    if v___x_1738_ == 0 {
                        v___x_1739_ = l_Float_fromJson_x3f___closed__4;
                        v___x_1740_ = lean_string_dec_eq(v_s_1731_, v___x_1739_);
                        leanh::lean_dec_ref(v_s_1731_);
                        if v___x_1740_ == 0 {
                            leanh::lean_del_object(v___x_1733_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1741_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1742_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1743_ =
                                l_Float_ofScientific(v___x_1741_, v___x_1740_, v___x_1742_);
                            v___x_1744_ = lean_float_div(v___x_1743_, v___x_1743_);
                            v___x_1745_ = leanh::lean_box_float(v___x_1744_);
                            if v_isShared_1734_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_1733_, 1);
                                leanh::lean_ctor_set(v___x_1733_, 0, v___x_1745_);
                                v___x_1747_ = v___x_1733_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1748_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
                                v___x_1747_ = v_reuseFailAlloc_1748_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_s_1731_);
                        v___x_1749_ = leanh::lean_unsigned_to_nat(10);
                        v___x_1750_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1751_ = l_Float_ofScientific(v___x_1749_, v___x_1738_, v___x_1750_);
                        v___x_1752_ = lean_float_negate(v___x_1751_);
                        v___x_1753_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1754_ = l_Float_ofScientific(v___x_1753_, v___x_1738_, v___x_1750_);
                        v___x_1755_ = lean_float_div(v___x_1752_, v___x_1754_);
                        v___x_1756_ = leanh::lean_box_float(v___x_1755_);
                        if v_isShared_1734_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1733_, 1);
                            leanh::lean_ctor_set(v___x_1733_, 0, v___x_1756_);
                            v___x_1758_ = v___x_1733_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1759_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
                            v___x_1758_ = v_reuseFailAlloc_1759_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_s_1731_);
                    v___x_1760_ = leanh::lean_unsigned_to_nat(10);
                    v___x_1761_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1762_ = l_Float_ofScientific(v___x_1760_, v___x_1736_, v___x_1761_);
                    v___x_1763_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1764_ = l_Float_ofScientific(v___x_1763_, v___x_1736_, v___x_1761_);
                    v___x_1765_ = lean_float_div(v___x_1762_, v___x_1764_);
                    v___x_1766_ = leanh::lean_box_float(v___x_1765_);
                    if v_isShared_1734_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1733_, 1);
                        leanh::lean_ctor_set(v___x_1733_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1733_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1747_;
            }
            4 => {
                return v___x_1758_;
            }
            5 => {
                return v___x_1768_;
            }
            6 => {
                v___x_1775_ = l_Lean_JsonNumber_toFloat(v_n_1771_);
                v___x_1776_ = leanh::lean_box_float(v___x_1775_);
                if v_isShared_1774_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1773_, 1);
                    leanh::lean_ctor_set(v___x_1773_, 0, v___x_1776_);
                    v___x_1778_ = v___x_1773_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
                    v___x_1778_ = v_reuseFailAlloc_1779_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Structured_fromJson_x3f(
    mut v_x_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elems_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_kvPairs_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1784_) {
                4 => {
                    v_elems_1785_ = leanh::lean_ctor_get(v_x_1784_, 0);
                    v_isSharedCheck_1793_ = (!leanh::lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1787_ = v_x_1784_;
                        v_isShared_1788_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_elems_1785_);
                        leanh::lean_dec(v_x_1784_);
                        v___x_1787_ = leanh::lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_kvPairs_1794_ = leanh::lean_ctor_get(v_x_1784_, 0);
                    v_isSharedCheck_1802_ = (!leanh::lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1802_ == 0 {
                        v___x_1796_ = v_x_1784_;
                        v_isShared_1797_ = v_isSharedCheck_1802_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_kvPairs_1794_);
                        leanh::lean_dec(v_x_1784_);
                        v___x_1796_ = leanh::lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1802_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1803_ = l_Lean_Json_Structured_fromJson_x3f___closed__0;
                    v___x_1804_ = leanh::lean_unsigned_to_nat(80);
                    v___x_1805_ = l_Lean_Json_pretty(v_x_1784_, v___x_1804_);
                    v___x_1806_ = lean_string_append(v___x_1803_, v___x_1805_);
                    leanh::lean_dec_ref(v___x_1805_);
                    v___x_1807_ = l_Array_fromJson_x3f___redArg___closed__11;
                    v___x_1808_ = lean_string_append(v___x_1806_, v___x_1807_);
                    v___x_1809_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                    return v___x_1809_;
                }
            },
            1 => {
                if v_isShared_1788_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1787_, 0);
                    v___x_1790_ = v___x_1787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_elems_1785_);
                    v___x_1790_ = v_reuseFailAlloc_1792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1791_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
                return v___x_1791_;
            }
            3 => {
                if v_isShared_1797_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1796_, 1);
                    v___x_1799_ = v___x_1796_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_kvPairs_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1800_, 0, v___x_1799_);
                return v___x_1800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Structured_toJson(
    mut v_x_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elems_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v_kvPairs_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1812_) == 0 {
                    v_elems_1813_ = leanh::lean_ctor_get(v_x_1812_, 0);
                    v_isSharedCheck_1820_ = (!leanh::lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1815_ = v_x_1812_;
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_elems_1813_);
                        leanh::lean_dec(v_x_1812_);
                        v___x_1815_ = leanh::lean_box(0);
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_kvPairs_1821_ = leanh::lean_ctor_get(v_x_1812_, 0);
                    v_isSharedCheck_1828_ = (!leanh::lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v_x_1812_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_kvPairs_1821_);
                        leanh::lean_dec(v_x_1812_);
                        v___x_1823_ = leanh::lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1816_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1815_, 4);
                    v___x_1818_ = v___x_1815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_elems_1813_);
                    v___x_1818_ = v_reuseFailAlloc_1819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1818_;
            }
            3 => {
                if v_isShared_1824_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1823_, 5);
                    v___x_1826_ = v___x_1823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_kvPairs_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_toStructured_x3f___redArg(
    mut v_inst_1831_: *mut leanh::LeanObject,
    mut v_v_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = leanh::lean_apply_1(v_inst_1831_, v_v_1832_);
    v___x_1834_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_Json_toStructured_x3f(
    mut v_00_u03b1_1835_: *mut leanh::LeanObject,
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_v_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_1836_, v_v_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___redArg(
    mut v_j_1839_: *mut leanh::LeanObject,
    mut v_inst_1840_: *mut leanh::LeanObject,
    mut v_k_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Lean_Json_getObjValD(v_j_1839_, v_k_1841_);
    v___x_1843_ = leanh::lean_apply_1(v_inst_1840_, v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___redArg___boxed(
    mut v_j_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_k_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1844_, v_inst_1845_, v_k_1846_);
    leanh::lean_dec_ref(v_k_1846_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f(
    mut v_j_1848_: *mut leanh::LeanObject,
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_inst_1850_: *mut leanh::LeanObject,
    mut v_k_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1848_, v_inst_1850_, v_k_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___boxed(
    mut v_j_1853_: *mut leanh::LeanObject,
    mut v_00_u03b1_1854_: *mut leanh::LeanObject,
    mut v_inst_1855_: *mut leanh::LeanObject,
    mut v_k_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Lean_Json_getObjValAs_x3f(v_j_1853_, v_00_u03b1_1854_, v_inst_1855_, v_k_1856_);
    leanh::lean_dec_ref(v_k_1856_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_Json_setObjValAs_x21___redArg(
    mut v_j_1858_: *mut leanh::LeanObject,
    mut v_inst_1859_: *mut leanh::LeanObject,
    mut v_k_1860_: *mut leanh::LeanObject,
    mut v_v_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = leanh::lean_apply_1(v_inst_1859_, v_v_1861_);
    v___x_1863_ = l_Lean_Json_setObjVal_x21(v_j_1858_, v_k_1860_, v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_Json_setObjValAs_x21(
    mut v_j_1864_: *mut leanh::LeanObject,
    mut v_00_u03b1_1865_: *mut leanh::LeanObject,
    mut v_inst_1866_: *mut leanh::LeanObject,
    mut v_k_1867_: *mut leanh::LeanObject,
    mut v_v_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ =
        l_Lean_Json_setObjValAs_x21___redArg(v_j_1864_, v_inst_1866_, v_k_1867_, v_v_1868_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_Json_opt___redArg(
    mut v_inst_1870_: *mut leanh::LeanObject,
    mut v_k_1871_: *mut leanh::LeanObject,
    mut v_x_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1872_) == 0 {
        let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_1871_);
        leanh::lean_dec_ref(v_inst_1870_);
        v___x_1873_ = leanh::lean_box(0);
        return v___x_1873_;
    } else {
        let mut v_val_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1874_ = leanh::lean_ctor_get(v_x_1872_, 0);
        leanh::lean_inc(v_val_1874_);
        leanh::lean_dec_ref_known(v_x_1872_, 1);
        v___x_1875_ = leanh::lean_apply_1(v_inst_1870_, v_val_1874_);
        v___x_1876_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1876_, 0, v_k_1871_);
        leanh::lean_ctor_set(v___x_1876_, 1, v___x_1875_);
        v___x_1877_ = leanh::lean_box(0);
        v___x_1878_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1878_, 0, v___x_1876_);
        leanh::lean_ctor_set(v___x_1878_, 1, v___x_1877_);
        return v___x_1878_;
    }
}
pub unsafe fn l_Lean_Json_opt(
    mut v_00_u03b1_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_k_1881_: *mut leanh::LeanObject,
    mut v_x_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lean_Json_opt___redArg(v_inst_1880_, v_k_1881_, v_x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_Json_getTag_x3f(
    mut v_x_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1892_: u8 = 0;
    let mut v_kvPairs_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1884_) {
                3 => {
                    v_s_1885_ = leanh::lean_ctor_get(v_x_1884_, 0);
                    v_isSharedCheck_1892_ = (!leanh::lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1892_ == 0 {
                        v___x_1887_ = v_x_1884_;
                        v_isShared_1888_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_1885_);
                        leanh::lean_dec(v_x_1884_);
                        v___x_1887_ = leanh::lean_box(0);
                        v_isShared_1888_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_kvPairs_1893_ = leanh::lean_ctor_get(v_x_1884_, 0);
                    leanh::lean_inc(v_kvPairs_1893_);
                    leanh::lean_dec_ref_known(v_x_1884_, 1);
                    if leanh::lean_obj_tag(v_kvPairs_1893_) == 0 {
                        v_size_1900_ = leanh::lean_ctor_get(v_kvPairs_1893_, 0);
                        leanh::lean_inc(v_size_1900_);
                        v___y_1895_ = v_size_1900_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1901_ = leanh::lean_unsigned_to_nat(0);
                        v___y_1895_ = v___x_1901_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_1884_);
                    v___x_1902_ = leanh::lean_box(0);
                    return v___x_1902_;
                }
            },
            1 => {
                if v_isShared_1888_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1887_, 1);
                    v___x_1890_ = v___x_1887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_s_1885_);
                    v___x_1890_ = v_reuseFailAlloc_1891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1890_;
            }
            3 => {
                v___x_1896_ = leanh::lean_unsigned_to_nat(1);
                v___x_1897_ = lean_nat_dec_eq(v___y_1895_, v___x_1896_);
                leanh::lean_dec(v___y_1895_);
                if v___x_1897_ == 0 {
                    leanh::lean_dec(v_kvPairs_1893_);
                    v___x_1898_ = leanh::lean_box(0);
                    return v___x_1898_;
                } else {
                    v___x_1899_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_kvPairs_1893_);
                    leanh::lean_dec(v_kvPairs_1893_);
                    return v___x_1899_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_as_1904_: *mut leanh::LeanObject,
    mut v_sz_1905_: usize,
    mut v_i_1906_: usize,
    mut v_b_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v_a_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: usize = 0;
    let mut v___x_1924_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1908_ = lean_usize_dec_lt(v_i_1906_, v_sz_1905_);
                if v___x_1908_ == 0 {
                    leanh::lean_dec(v_a_1903_);
                    v___x_1909_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1909_, 0, v_b_1907_);
                    return v___x_1909_;
                } else {
                    v_a_1910_ = lean_array_uget_borrowed(v_as_1904_, v_i_1906_);
                    v___x_1911_ = l_Lean_Name_getString_x21(v_a_1910_);
                    leanh::lean_inc(v_a_1903_);
                    v___x_1912_ = l_Lean_Json_getObjVal_x3f(v_a_1903_, v___x_1911_);
                    leanh::lean_dec_ref(v___x_1911_);
                    if leanh::lean_obj_tag(v___x_1912_) == 0 {
                        leanh::lean_dec_ref(v_b_1907_);
                        leanh::lean_dec(v_a_1903_);
                        v_a_1913_ = leanh::lean_ctor_get(v___x_1912_, 0);
                        v_isSharedCheck_1920_ =
                            (!leanh::lean_is_exclusive(v___x_1912_)) as u8;
                        if v_isSharedCheck_1920_ == 0 {
                            v___x_1915_ = v___x_1912_;
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1913_);
                            leanh::lean_dec(v___x_1912_);
                            v___x_1915_ = leanh::lean_box(0);
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1921_ = leanh::lean_ctor_get(v___x_1912_, 0);
                        leanh::lean_inc(v_a_1921_);
                        leanh::lean_dec_ref_known(v___x_1912_, 1);
                        v___x_1922_ = lean_array_push(v_b_1907_, v_a_1921_);
                        v___x_1923_ = 1usize;
                        v___x_1924_ = lean_usize_add(v_i_1906_, v___x_1923_);
                        v_i_1906_ = v___x_1924_;
                        v_b_1907_ = v___x_1922_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1916_ == 0 {
                    v___x_1918_ = v___x_1915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(
    mut v_a_1926_: *mut leanh::LeanObject,
    mut v_as_1927_: *mut leanh::LeanObject,
    mut v_sz_1928_: *mut leanh::LeanObject,
    mut v_i_1929_: *mut leanh::LeanObject,
    mut v_b_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1931_: usize = 0;
    let mut v_i_boxed_1932_: usize = 0;
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1931_ = leanh::lean_unbox_usize(v_sz_1928_);
    leanh::lean_dec(v_sz_1928_);
    v_i_boxed_1932_ = leanh::lean_unbox_usize(v_i_1929_);
    leanh::lean_dec(v_i_1929_);
    v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_1926_, v_as_1927_, v_sz_boxed_1931_, v_i_boxed_1932_, v_b_1930_);
    leanh::lean_dec_ref(v_as_1927_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_Json_parseTagged(
    mut v_json_1941_: *mut leanh::LeanObject,
    mut v_tag_1942_: *mut leanh::LeanObject,
    mut v_nFields_1943_: *mut leanh::LeanObject,
    mut v_fieldNames_x3f_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_a_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_unused_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_a_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: u8 = 0;
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1945_ = leanh::lean_unsigned_to_nat(0);
                v___x_1946_ = lean_nat_dec_eq(v_nFields_1943_, v___x_1945_);
                if v___x_1946_ == 0 {
                    v___x_1947_ = l_Lean_Json_getObjVal_x3f(v_json_1941_, v_tag_1942_);
                    if leanh::lean_obj_tag(v___x_1947_) == 0 {
                        leanh::lean_dec(v_nFields_1943_);
                        v_a_1948_ = leanh::lean_ctor_get(v___x_1947_, 0);
                        v_isSharedCheck_1955_ =
                            (!leanh::lean_is_exclusive(v___x_1947_)) as u8;
                        if v_isSharedCheck_1955_ == 0 {
                            v___x_1950_ = v___x_1947_;
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1948_);
                            leanh::lean_dec(v___x_1947_);
                            v___x_1950_ = leanh::lean_box(0);
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_fieldNames_x3f_1944_) == 0 {
                            v_a_1956_ = leanh::lean_ctor_get(v___x_1947_, 0);
                            v_isSharedCheck_1986_ =
                                (!leanh::lean_is_exclusive(v___x_1947_)) as u8;
                            if v_isSharedCheck_1986_ == 0 {
                                v___x_1958_ = v___x_1947_;
                                v_isShared_1959_ = v_isSharedCheck_1986_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1956_);
                                leanh::lean_dec(v___x_1947_);
                                v___x_1958_ = leanh::lean_box(0);
                                v_isShared_1959_ = v_isSharedCheck_1986_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_nFields_1943_);
                            v_a_1987_ = leanh::lean_ctor_get(v___x_1947_, 0);
                            leanh::lean_inc(v_a_1987_);
                            leanh::lean_dec_ref_known(v___x_1947_, 1);
                            v_val_1988_ = leanh::lean_ctor_get(v_fieldNames_x3f_1944_, 0);
                            v_fields_1989_ = l_Lean_Json_parseTagged___closed__2;
                            v_sz_1990_ = lean_array_size(v_val_1988_);
                            v___x_1991_ = 0usize;
                            v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_1987_, v_val_1988_, v_sz_1990_, v___x_1991_, v_fields_1989_);
                            return v___x_1992_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_nFields_1943_);
                    v___x_1993_ = l_Lean_Json_getStr_x3f(v_json_1941_);
                    if leanh::lean_obj_tag(v___x_1993_) == 0 {
                        v_a_1994_ = leanh::lean_ctor_get(v___x_1993_, 0);
                        v_isSharedCheck_2001_ =
                            (!leanh::lean_is_exclusive(v___x_1993_)) as u8;
                        if v_isSharedCheck_2001_ == 0 {
                            v___x_1996_ = v___x_1993_;
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1994_);
                            leanh::lean_dec(v___x_1993_);
                            v___x_1996_ = leanh::lean_box(0);
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_2002_ = leanh::lean_ctor_get(v___x_1993_, 0);
                        v_isSharedCheck_2016_ =
                            (!leanh::lean_is_exclusive(v___x_1993_)) as u8;
                        if v_isSharedCheck_2016_ == 0 {
                            v___x_2004_ = v___x_1993_;
                            v_isShared_2005_ = v_isSharedCheck_2016_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2002_);
                            leanh::lean_dec(v___x_1993_);
                            v___x_2004_ = leanh::lean_box(0);
                            v_isShared_2005_ = v_isSharedCheck_2016_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1951_ == 0 {
                    v___x_1953_ = v___x_1950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
                    v___x_1953_ = v_reuseFailAlloc_1954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1953_;
            }
            3 => {
                v___x_1960_ = leanh::lean_unsigned_to_nat(1);
                v___x_1961_ = lean_nat_dec_eq(v_nFields_1943_, v___x_1960_);
                if v___x_1961_ == 0 {
                    leanh::lean_del_object(v___x_1958_);
                    v___x_1962_ = l_Lean_Json_getArr_x3f(v_a_1956_);
                    if leanh::lean_obj_tag(v___x_1962_) == 0 {
                        leanh::lean_dec(v_nFields_1943_);
                        return v___x_1962_;
                    } else {
                        v_a_1963_ = leanh::lean_ctor_get(v___x_1962_, 0);
                        leanh::lean_inc(v_a_1963_);
                        v___x_1964_ = lean_array_get_size(v_a_1963_);
                        leanh::lean_dec(v_a_1963_);
                        v___x_1965_ = lean_nat_dec_eq(v___x_1964_, v_nFields_1943_);
                        if v___x_1965_ == 0 {
                            v_isSharedCheck_1979_ =
                                (!leanh::lean_is_exclusive(v___x_1962_)) as u8;
                            if v_isSharedCheck_1979_ == 0 {
                                v_unused_1980_ = leanh::lean_ctor_get(v___x_1962_, 0);
                                leanh::lean_dec(v_unused_1980_);
                                v___x_1967_ = v___x_1962_;
                                v_isShared_1968_ = v_isSharedCheck_1979_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1962_);
                                v___x_1967_ = leanh::lean_box(0);
                                v_isShared_1968_ = v_isSharedCheck_1979_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_nFields_1943_);
                            return v___x_1962_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_nFields_1943_);
                    v___x_1981_ = lean_mk_empty_array_with_capacity(v___x_1960_);
                    v___x_1982_ = lean_array_push(v___x_1981_, v_a_1956_);
                    if v_isShared_1959_ == 0 {
                        leanh::lean_ctor_set(v___x_1958_, 0, v___x_1982_);
                        v___x_1984_ = v___x_1958_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
                        v___x_1984_ = v_reuseFailAlloc_1985_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1969_ = l_Lean_Json_parseTagged___closed__0;
                v___x_1970_ = l_Nat_reprFast(v___x_1964_);
                v___x_1971_ = lean_string_append(v___x_1969_, v___x_1970_);
                leanh::lean_dec_ref(v___x_1970_);
                v___x_1972_ = l_Lean_Json_parseTagged___closed__1;
                v___x_1973_ = lean_string_append(v___x_1971_, v___x_1972_);
                v___x_1974_ = l_Nat_reprFast(v_nFields_1943_);
                v___x_1975_ = lean_string_append(v___x_1973_, v___x_1974_);
                leanh::lean_dec_ref(v___x_1974_);
                if v_isShared_1968_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1967_, 0);
                    leanh::lean_ctor_set(v___x_1967_, 0, v___x_1975_);
                    v___x_1977_ = v___x_1967_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
                    v___x_1977_ = v_reuseFailAlloc_1978_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1977_;
            }
            6 => {
                return v___x_1984_;
            }
            7 => {
                if v_isShared_1997_ == 0 {
                    v___x_1999_ = v___x_1996_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
                    v___x_1999_ = v_reuseFailAlloc_2000_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1999_;
            }
            9 => {
                v___x_2006_ = lean_string_dec_eq(v_a_2002_, v_tag_1942_);
                if v___x_2006_ == 0 {
                    v___x_2007_ = l_Lean_Json_parseTagged___closed__3;
                    v___x_2008_ = lean_string_append(v___x_2007_, v_a_2002_);
                    leanh::lean_dec(v_a_2002_);
                    v___x_2009_ = l_Lean_Json_parseTagged___closed__1;
                    v___x_2010_ = lean_string_append(v___x_2008_, v___x_2009_);
                    v___x_2011_ = lean_string_append(v___x_2010_, v_tag_1942_);
                    if v_isShared_2005_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2004_, 0);
                        leanh::lean_ctor_set(v___x_2004_, 0, v___x_2011_);
                        v___x_2013_ = v___x_2004_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2014_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
                        v___x_2013_ = v_reuseFailAlloc_2014_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2004_);
                    leanh::lean_dec(v_a_2002_);
                    v___x_2015_ = l_Lean_Json_parseTagged___closed__4;
                    return v___x_2015_;
                }
            }
            10 => {
                return v___x_2013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_parseTagged___boxed(
    mut v_json_2017_: *mut leanh::LeanObject,
    mut v_tag_2018_: *mut leanh::LeanObject,
    mut v_nFields_2019_: *mut leanh::LeanObject,
    mut v_fieldNames_x3f_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Lean_Json_parseTagged(
        v_json_2017_,
        v_tag_2018_,
        v_nFields_2019_,
        v_fieldNames_x3f_2020_,
    );
    leanh::lean_dec(v_fieldNames_x3f_2020_);
    leanh::lean_dec_ref(v_tag_2018_);
    return v_res_2021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(
    mut v_a_2022_: *mut leanh::LeanObject,
    mut v_sz_2023_: usize,
    mut v_i_2024_: usize,
    mut v_bs_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_a_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: usize = 0;
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2026_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
                if v___x_2026_ == 0 {
                    leanh::lean_dec(v_a_2022_);
                    v___x_2027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2027_, 0, v_bs_2025_);
                    return v___x_2027_;
                } else {
                    v_v_2028_ = lean_array_uget_borrowed(v_bs_2025_, v_i_2024_);
                    v___x_2029_ = l_Lean_Name_getString_x21(v_v_2028_);
                    leanh::lean_inc(v_a_2022_);
                    v___x_2030_ = l_Lean_Json_getObjVal_x3f(v_a_2022_, v___x_2029_);
                    leanh::lean_dec_ref(v___x_2029_);
                    if leanh::lean_obj_tag(v___x_2030_) == 0 {
                        leanh::lean_dec_ref(v_bs_2025_);
                        leanh::lean_dec(v_a_2022_);
                        v_a_2031_ = leanh::lean_ctor_get(v___x_2030_, 0);
                        v_isSharedCheck_2038_ =
                            (!leanh::lean_is_exclusive(v___x_2030_)) as u8;
                        if v_isSharedCheck_2038_ == 0 {
                            v___x_2033_ = v___x_2030_;
                            v_isShared_2034_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2031_);
                            leanh::lean_dec(v___x_2030_);
                            v___x_2033_ = leanh::lean_box(0);
                            v_isShared_2034_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2039_ = leanh::lean_ctor_get(v___x_2030_, 0);
                        leanh::lean_inc(v_a_2039_);
                        leanh::lean_dec_ref_known(v___x_2030_, 1);
                        v___x_2040_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2041_ = lean_array_uset(v_bs_2025_, v_i_2024_, v___x_2040_);
                        v___x_2042_ = 1usize;
                        v___x_2043_ = lean_usize_add(v_i_2024_, v___x_2042_);
                        v___x_2044_ = lean_array_uset(v_bs_x27_2041_, v_i_2024_, v_a_2039_);
                        v_i_2024_ = v___x_2043_;
                        v_bs_2025_ = v___x_2044_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2034_ == 0 {
                    v___x_2036_ = v___x_2033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(
    mut v_a_2046_: *mut leanh::LeanObject,
    mut v_sz_2047_: *mut leanh::LeanObject,
    mut v_i_2048_: *mut leanh::LeanObject,
    mut v_bs_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2050_: usize = 0;
    let mut v_i_boxed_2051_: usize = 0;
    let mut v_res_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2050_ = leanh::lean_unbox_usize(v_sz_2047_);
    leanh::lean_dec(v_sz_2047_);
    v_i_boxed_2051_ = leanh::lean_unbox_usize(v_i_2048_);
    leanh::lean_dec(v_i_2048_);
    v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_2046_, v_sz_boxed_2050_, v_i_boxed_2051_, v_bs_2049_);
    return v_res_2052_;
}
pub unsafe fn l_Lean_Json_parseCtorFields(
    mut v_json_2053_: *mut leanh::LeanObject,
    mut v_tag_2054_: *mut leanh::LeanObject,
    mut v_nFields_2055_: *mut leanh::LeanObject,
    mut v_fieldNames_x3f_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v_a_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2078_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2099_: usize = 0;
    let mut v___x_2100_: usize = 0;
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2057_ = l_Lean_Json_getObjVal_x3f(v_json_2053_, v_tag_2054_);
                if leanh::lean_obj_tag(v___x_2057_) == 0 {
                    leanh::lean_dec(v_fieldNames_x3f_2056_);
                    leanh::lean_dec(v_nFields_2055_);
                    v_a_2058_ = leanh::lean_ctor_get(v___x_2057_, 0);
                    v_isSharedCheck_2065_ = (!leanh::lean_is_exclusive(v___x_2057_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2060_ = v___x_2057_;
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2058_);
                        leanh::lean_dec(v___x_2057_);
                        v___x_2060_ = leanh::lean_box(0);
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v_fieldNames_x3f_2056_) == 0 {
                        v_a_2066_ = leanh::lean_ctor_get(v___x_2057_, 0);
                        v_isSharedCheck_2096_ =
                            (!leanh::lean_is_exclusive(v___x_2057_)) as u8;
                        if v_isSharedCheck_2096_ == 0 {
                            v___x_2068_ = v___x_2057_;
                            v_isShared_2069_ = v_isSharedCheck_2096_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2066_);
                            leanh::lean_dec(v___x_2057_);
                            v___x_2068_ = leanh::lean_box(0);
                            v_isShared_2069_ = v_isSharedCheck_2096_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_nFields_2055_);
                        v_a_2097_ = leanh::lean_ctor_get(v___x_2057_, 0);
                        leanh::lean_inc(v_a_2097_);
                        leanh::lean_dec_ref_known(v___x_2057_, 1);
                        v_val_2098_ = leanh::lean_ctor_get(v_fieldNames_x3f_2056_, 0);
                        leanh::lean_inc(v_val_2098_);
                        leanh::lean_dec_ref_known(v_fieldNames_x3f_2056_, 1);
                        v_sz_2099_ = lean_array_size(v_val_2098_);
                        v___x_2100_ = 0usize;
                        v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_2097_, v_sz_2099_, v___x_2100_, v_val_2098_);
                        return v___x_2101_;
                    }
                }
            }
            1 => {
                if v_isShared_2061_ == 0 {
                    v___x_2063_ = v___x_2060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2063_;
            }
            3 => {
                v___x_2070_ = leanh::lean_unsigned_to_nat(1);
                v___x_2071_ = lean_nat_dec_eq(v_nFields_2055_, v___x_2070_);
                if v___x_2071_ == 0 {
                    leanh::lean_del_object(v___x_2068_);
                    v___x_2072_ = l_Lean_Json_getArr_x3f(v_a_2066_);
                    if leanh::lean_obj_tag(v___x_2072_) == 0 {
                        leanh::lean_dec(v_nFields_2055_);
                        return v___x_2072_;
                    } else {
                        v_a_2073_ = leanh::lean_ctor_get(v___x_2072_, 0);
                        leanh::lean_inc(v_a_2073_);
                        v___x_2074_ = lean_array_get_size(v_a_2073_);
                        leanh::lean_dec(v_a_2073_);
                        v___x_2075_ = lean_nat_dec_eq(v___x_2074_, v_nFields_2055_);
                        if v___x_2075_ == 0 {
                            v_isSharedCheck_2089_ =
                                (!leanh::lean_is_exclusive(v___x_2072_)) as u8;
                            if v_isSharedCheck_2089_ == 0 {
                                v_unused_2090_ = leanh::lean_ctor_get(v___x_2072_, 0);
                                leanh::lean_dec(v_unused_2090_);
                                v___x_2077_ = v___x_2072_;
                                v_isShared_2078_ = v_isSharedCheck_2089_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2072_);
                                v___x_2077_ = leanh::lean_box(0);
                                v_isShared_2078_ = v_isSharedCheck_2089_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_nFields_2055_);
                            return v___x_2072_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_nFields_2055_);
                    v___x_2091_ = lean_mk_empty_array_with_capacity(v___x_2070_);
                    v___x_2092_ = lean_array_push(v___x_2091_, v_a_2066_);
                    if v_isShared_2069_ == 0 {
                        leanh::lean_ctor_set(v___x_2068_, 0, v___x_2092_);
                        v___x_2094_ = v___x_2068_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
                        v___x_2094_ = v_reuseFailAlloc_2095_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2079_ = l_Lean_Json_parseTagged___closed__0;
                v___x_2080_ = l_Nat_reprFast(v___x_2074_);
                v___x_2081_ = lean_string_append(v___x_2079_, v___x_2080_);
                leanh::lean_dec_ref(v___x_2080_);
                v___x_2082_ = l_Lean_Json_parseTagged___closed__1;
                v___x_2083_ = lean_string_append(v___x_2081_, v___x_2082_);
                v___x_2084_ = l_Nat_reprFast(v_nFields_2055_);
                v___x_2085_ = lean_string_append(v___x_2083_, v___x_2084_);
                leanh::lean_dec_ref(v___x_2084_);
                if v_isShared_2078_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2077_, 0);
                    leanh::lean_ctor_set(v___x_2077_, 0, v___x_2085_);
                    v___x_2087_ = v___x_2077_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2087_;
            }
            6 => {
                return v___x_2094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_parseCtorFields___boxed(
    mut v_json_2102_: *mut leanh::LeanObject,
    mut v_tag_2103_: *mut leanh::LeanObject,
    mut v_nFields_2104_: *mut leanh::LeanObject,
    mut v_fieldNames_x3f_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_Lean_Json_parseCtorFields(
        v_json_2102_,
        v_tag_2103_,
        v_nFields_2104_,
        v_fieldNames_x3f_2105_,
    );
    leanh::lean_dec_ref(v_tag_2103_);
    return v_res_2106_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_FromToJson_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Printer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_GetLit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_FromToJson_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_FromToJson_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Printer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_GetLit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Json_FromToJson_Basic(builtin);
}